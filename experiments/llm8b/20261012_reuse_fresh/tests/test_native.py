"""Exercise the entire logging/state/reconstruction contract on a tiny random model."""
from pathlib import Path
import sys,tempfile,json
import numpy as np
import torch
from transformers import Qwen3Config,Qwen3ForCausalLM
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from run import run_path
from design import step_optimism
import copy

def main():
 torch.set_num_threads(1);torch.manual_seed(71)
 config=Qwen3Config(vocab_size=256,hidden_size=128,intermediate_size=256,num_hidden_layers=2,
   num_attention_heads=4,num_key_value_heads=2,head_dim=32)
 config._attn_implementation='sdpa'
 teacher=Qwen3ForCausalLM(config).to(torch.bfloat16).eval();student=copy.deepcopy(teacher)
 for p in teacher.parameters():p.requires_grad_(False)
 for p in student.parameters():p.requires_grad_(False)
 rng=np.random.default_rng(31);arrays={k:rng.integers(0,256,size=4096,dtype=np.int64) for k in ['train','eval','eval_extra']}
 starts=(np.arange(4,68)*16).reshape(8,8).tolist();fit_starts=[0,16,32,48]
 fit=torch.from_numpy(np.stack([arrays['train'][i:i+16] for i in fit_starts]))
 plan={'model':'toy','source_audit_starts':list(range(200*16,232*16,16)),
 'step_audit_starts':list(range(200*16,208*16,16)),'audit_ranges':{'eval':[16,16+32*16],'eval_extra':[16,16+32*16]},
 'draws':{'1':{'fresh':starts,'reuse':starts[0]},'2':{'fresh':starts[::-1],'reuse':starts[-1]}}}
 cfg={'sequence_length':16,'microbatch':8,'damping':1.,'bits':4,'group_size':128,'alphas':[0.,.5,1.],'step_audit_windows':8}
 with tempfile.TemporaryDirectory() as temp:
  results={};first=[]
  for policy,mode in [('rtn','fixed'),('qep_half','fixed'),('task_select','reuse'),('local_select','reuse'),('task_select','fresh'),('local_select','fresh')]:
   out=Path(temp)/f'{policy}_{mode}'
   run_path(teacher,student,arrays,fit,plan,cfg,policy,mode,1,out,'cpu')
   results[policy,mode]=json.loads((out/'results.json').read_text())
   records=list(map(json.loads,(out/'decisions.jsonl').read_text().splitlines()))
   assert len(records)==8
   if mode=='fixed':continue
   first.append(json.loads((out/'verification.json').read_text())['first_step_candidate_sha256'])
   assert all(len(c['selection_nll'])==len(c['selection_mse'])==len(c['audit_nll'])==8 for r in records for c in r['candidates'])
   if mode=='reuse':
    r=results[policy,mode]['final'];base=results['rtn','fixed']['final']
    path_o=(base['selection_by_draw']['1']['nll']-r['selection']['nll'])-(sum(base['source']['sequence_nll'][:8])/8-sum(r['source']['sequence_nll'][:8])/8)
    assert abs(sum(step_optimism(x)['optimism'] for x in records)-path_o)<1e-5
   else:
    assert 'selection' not in results[policy,mode]['final']
    assert len((out/'final_selection_windows.jsonl').read_text().splitlines())==8
  assert all(v==first[0] for v in first)
 print('PASS: complete tiny-model paths; all per-window matrices; audit telescoping; fresh unpooled records; candidate identity; native baseline reconstruction')
if __name__=='__main__':main()
