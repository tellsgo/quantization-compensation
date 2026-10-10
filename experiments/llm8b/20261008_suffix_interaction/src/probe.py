"""Replay historical candidates; intervene only on strictly later blocks."""
from pathlib import Path
import argparse,copy,json,time,hashlib,os
import numpy as np
import torch
import transformers
from transformers import AutoModelForCausalLM
from core import GROUPS,quantize,fit_map,correction,write_json
from scale_selection import capture_state,forward_state,suffix_value,append_json

def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

@torch.no_grad()
def run(a):
 out=Path(a.output);out.mkdir(parents=True,exist_ok=False)
 base=Path(a.base);meta=json.loads((base/'manifest.json').read_text())
 cfg=json.loads(Path(a.config).read_text());tol=cfg['score_tolerance'];start=time.time()
 assert meta['config']['selection_tokens']==cfg['selection_tokens']==4096
 torch.set_num_threads(4);torch.manual_seed(meta['config']['seed']);torch.backends.cuda.matmul.allow_tf32=False
 sources={}
 for name in ['probe.py','core.py','scale_selection.py']:
  path=Path(__file__).with_name(name);sources[name]=digest(path);(out/name).write_bytes(path.read_bytes())
 for name in ['core.py','scale_selection.py']:assert sources[name]==meta['source_sha256'][name]
 write_json(out/'manifest.json',{'args':vars(a),'config':cfg,'source_sha256':sources,'parent_manifest_sha256':digest(base/'manifest.json'),
   'parent_decisions_sha256':digest(base/'decisions.jsonl'),'torch':torch.__version__,'transformers':transformers.__version__,'start_unix':start,
   'gpu':torch.cuda.get_device_name(0),'visible_devices':os.environ.get('CUDA_VISIBLE_DEVICES')})
 (out/'parent_manifest.json').write_bytes((base/'manifest.json').read_bytes())
 data=json.loads((base/'data.json').read_text());tok={}
 for k in ['cal','select','diag']:
  v=np.load(base/f'{k}_tokens.npy');assert hashlib.sha256(v.tobytes()).hexdigest()==data['token_hashes'][k]
  np.save(out/f'{k}_tokens.npy',v);tok[k]=torch.from_numpy(v).cuda()
 write_json(out/'data.json',data)
 model=AutoModelForCausalLM.from_pretrained(meta['args']['model'],dtype=torch.bfloat16,attn_implementation='sdpa',local_files_only=True).cuda().eval()
 for v in model.parameters():v.requires_grad_(False)
 names=sum(GROUPS,[]);layers=model.model.layers;L=len(layers)
 rtn=copy.deepcopy(layers);complete=copy.deepcopy(layers)
 for li in range(L):
  for name in names:
   w=quantize(layers[li].get_submodule(name).weight,4,128)
   rtn[li].get_submodule(name).weight.copy_(w);complete[li].get_submodule(name).weight.copy_(w)
 schedule={}
 for line in (base/'decisions.jsonl').read_text().splitlines():
  r=json.loads(line)
  if r['policy']=='task_select':
   for c in r['choices']:schedule[r['layer'],c['group']]=c['alpha']
 assert len(schedule)==4*L
 old={(r['layer'],r['group']):r for r in map(json.loads,(base/'matched_state.jsonl').read_text().splitlines())}
 teacher=model.model.embed_tokens(tok['cal']);student=teacher.clone()
 rotary=model.model.rotary_emb(teacher,torch.arange(512,device='cuda').unsqueeze(0))
 # Rebuild the fixed completed suffix without changing any original teacher layers.
 for li,layer in enumerate(layers):
  weights={n:layer.get_submodule(n).weight.float().clone() for n in names}
  teacher_next,inputs=capture_state(layer,teacher,rotary,names)
  work=complete[li]
  for gi,group in enumerate(GROUPS):
   alpha=schedule[li,gi]
   if alpha:
    _,inp=capture_state(work,student,rotary,[group[0]])
    x=inputs[group[0]].reshape(-1,weights[group[0]].shape[1]);z=inp[group[0]].reshape_as(x);fit=fit_map(x,z,1.)
    for n in group:work.get_submodule(n).weight.copy_(quantize(weights[n]+alpha*correction(weights[n],fit),4,128))
    del inp,fit
  student=forward_state(work,student,rotary);teacher=teacher_next
  del weights,inputs
 reference=json.loads((base/'results.json').read_text());checks={}
 for k in ['select','diag']:
  val=suffix_value(model,complete,rotary,model.model.embed_tokens(tok[k]),tok[k],0)
  difference=abs(val-reference['policies']['task_select'][k]['nll']);assert difference<tol,(k,difference)
  checks[k]={'reconstructed_nll':val,'difference':difference}
 write_json(out/'reconstruction_checks.json',checks)
 print(json.dumps({'event':'reconstruction_pass','seconds':time.time()-start}),flush=True)
 teacher=model.model.embed_tokens(tok['cal']);state={k:model.model.embed_tokens(v) for k,v in tok.items()}
 audit={0,L//3,2*L//3,L-1};history_errors=[];last_errors=[]
 for li,layer in enumerate(layers):
  weights={n:layer.get_submodule(n).weight.float().clone() for n in names}
  teacher_next,inputs=capture_state(layer,teacher,rotary,names)
  # Only current block is mutated; completed suffix and RTN suffix stay immutable.
  for n in names:layer.get_submodule(n).weight.copy_(rtn[li].get_submodule(n).weight)
  for gi,group in enumerate(GROUPS):
   alpha=schedule[li,gi]
   if li in audit or alpha:
    _,inp=capture_state(layer,state['cal'],rotary,[group[0]])
    x=inputs[group[0]].reshape(-1,weights[group[0]].shape[1]);z=inp[group[0]].reshape_as(x);fit=fit_map(x,z,1.)
    delta={n:correction(weights[n],fit) for n in group}
    del inp,fit
    if li in audit:
     candidates=[]
     for candidate_alpha in [0.,.5,1.]:
      for n in group:layer.get_submodule(n).weight.copy_(quantize(weights[n]+candidate_alpha*delta[n],4,128))
      scores={}
      for k in ['select','diag']:
       h=forward_state(layer,state[k],rotary)
       scores[k]={tag:suffix_value(model,future,rotary,h,tok[k],li+1) for tag,future in [('rtn',rtn),('completed',complete)]}
       historical=next(c for c in old[li,gi]['candidates'] if c['alpha']==candidate_alpha)
       error=abs(scores[k]['rtn']-historical['task_nll' if k=='select' else 'diagnostic_nll'])
       assert error<tol,(li,gi,k,error);history_errors.append(error)
       if li==L-1:
        error=abs(scores[k]['rtn']-scores[k]['completed']);assert error==0;last_errors.append(error)
      candidates.append({'alpha':candidate_alpha,**scores})
     selected=min(candidates,key=lambda c:c['select']['rtn'])['alpha'];assert selected==alpha,(li,gi,selected,alpha)
     append_json(out/'interventions.jsonl',{'layer':li,'group':gi,'terminal_control':li==L-1,'historical_alpha':alpha,'candidates':candidates})
    for n in group:layer.get_submodule(n).weight.copy_(quantize(weights[n]+alpha*delta[n],4,128))
    del delta
  for k in state:state[k]=forward_state(layer,state[k],rotary)
  teacher=teacher_next;del weights,inputs
  if li in audit:print(json.dumps({'event':'audit_block','layer':li,'seconds':time.time()-start}),flush=True)
 # Auditing must not have modified the historical trajectory.
 for k in ['select','diag']:
  val=suffix_value(model,[],rotary,state[k],tok[k],0)
  assert abs(val-reference['policies']['task_select'][k]['nll'])<tol
 write_json(out/'checks.json',{'historical_candidate_max_error':max(history_errors),'historical_candidate_comparisons':len(history_errors),
 'terminal_max_difference':max(last_errors),'terminal_comparisons':len(last_errors),'final_trajectory_parity':'pass'})
 write_json(out/'progress.json',{'status':'complete','seconds':time.time()-start,'audited_groups':16})
 print(json.dumps({'event':'complete','seconds':time.time()-start}),flush=True)

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--base',required=True);p.add_argument('--output',required=True);p.add_argument('--config',required=True);a=p.parse_args()
 try:run(a)
 except Exception as e:
  if Path(a.output).exists():write_json(Path(a.output)/'failure.json',{'type':type(e).__name__,'message':str(e)})
  raise
