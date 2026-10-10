"""Rebuild a recorded correction schedule, then evaluate the native whole model.

This checks multi-policy state bookkeeping and candidate installation. It reuses
the independently unit-tested ridge helper, so is not an independent ridge proof.
"""
from pathlib import Path
import argparse,hashlib,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
import numpy as np
import torch
import torch.nn.functional as F
from transformers import AutoModelForCausalLM
from core import GROUPS,quantize,fit_map,correction,capture,block_forward,write_json

@torch.inference_mode()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--run',type=Path,required=True)
 ap.add_argument('--policy',choices=['block_select','task_select'],required=True)
 ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 assert not a.output.exists()
 meta=json.loads((a.run/'manifest.json').read_text());ref=json.loads((a.run/'results.json').read_text())
 dependency=Path(__file__).resolve().parents[1]/'src/core.py'
 assert hashlib.sha256(dependency.read_bytes()).hexdigest()==meta['source_sha256']['core.py']
 torch.set_num_threads(4);torch.backends.cuda.matmul.allow_tf32=False
 torch.manual_seed(meta['config']['seed'])
 model=AutoModelForCausalLM.from_pretrained(meta['args']['model'],dtype=torch.bfloat16,
     attn_implementation='sdpa',local_files_only=True).cuda().eval()
 cal=torch.from_numpy(np.load(a.run/'cal_tokens.npy')).cuda()
 teacher=model.model.embed_tokens(cal);student=teacher.clone()
 rotary=model.model.rotary_emb(teacher,torch.arange(512,device='cuda').unsqueeze(0))
 schedule={}
 for line in (a.run/'decisions.jsonl').read_text().splitlines():
  row=json.loads(line)
  if row['policy']==a.policy:
   for c in row['choices']:schedule[row['layer'],c['group']]=c['alpha']
 assert len(schedule)==len(model.model.layers)*4
 names=sum(GROUPS,[])
 for li,layer in enumerate(model.model.layers):
  weights={n:layer.get_submodule(n).weight.float().clone() for n in names}
  teacher_next,inputs=capture(layer,teacher,rotary,names)
  for n in names:layer.get_submodule(n).weight.copy_(quantize(weights[n],4,128))
  for gi,group in enumerate(GROUPS):
   alpha=schedule[li,gi]
   if alpha==0:continue
   _,sinput=capture(layer,student,rotary,[group[0]])
   x=inputs[group[0]].reshape(-1,weights[group[0]].shape[1]);z=sinput[group[0]].reshape_as(x)
   fit=fit_map(x,z,1.)
   for n in group:layer.get_submodule(n).weight.copy_(quantize(weights[n]+alpha*correction(weights[n],fit),4,128))
  student=block_forward(layer,student,rotary);teacher=teacher_next
 evidence={}
 for split in ['select','diag','eval','eval_extra']:
  tokens=torch.from_numpy(np.load(a.run/f'{split}_tokens.npy')).cuda();losses=[]
  for lo in range(0,len(tokens),8):
   batch=tokens[lo:lo+8]
   hidden=model.model(input_ids=batch,use_cache=False).last_hidden_state
   for i in range(len(batch)):
    logits=model.lm_head(hidden[i:i+1])
    losses.append(float(F.cross_entropy(logits[:,:-1].float().reshape(-1,logits.shape[-1]),batch[i:i+1,1:].reshape(-1))))
  expected=ref['policies'][a.policy][split]
  error=max(abs(x-y) for x,y in zip(losses,expected['sequence_nll']))
  assert len(losses)==len(expected['sequence_nll'])
  assert error<1e-6,(split,error)
  evidence[split]={'nll':sum(losses)/len(losses),'recorded_nll':expected['nll'],'max_sequence_difference':error}
 a.output.parent.mkdir(parents=True,exist_ok=True)
 write_json(a.output,{'run':a.run.name,'policy':a.policy,'checks':evidence,
   'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()})
 print(json.dumps({'run':a.run.name,'policy':a.policy,'checks':evidence}),flush=True)

if __name__=='__main__':main()
