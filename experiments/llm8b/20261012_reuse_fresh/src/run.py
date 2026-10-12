"""Fixed-fit selection reuse intervention, with audit scores isolated from selection."""
from pathlib import Path
import argparse,copy,hashlib,json,math,os,statistics as st,time
import numpy as np
import torch
import torch.nn.functional as F
import transformers
from transformers import AutoModelForCausalLM
from core import GROUPS,quantize,fit_map,correction,write_json
from scale_selection import forward_state,capture_state,append_json
from design import choose
ROOT=Path(__file__).resolve().parents[1]
NAMES=sum(GROUPS,[])
def sha(raw):return hashlib.sha256(raw).hexdigest()
def sync(device):
 if torch.device(device).type=='cuda':torch.cuda.synchronize(device)
def tensor_hash(t):return sha(t.detach().contiguous().view(torch.uint8).cpu().numpy().tobytes())
def checked_freeze():
 manifest=json.loads((ROOT/'docs/specs/FROZEN.json').read_text())
 for name,digest in manifest['files'].items():assert sha((ROOT/name).read_bytes())==digest,name
 return sha((ROOT/'docs/specs/FROZEN.json').read_bytes())
def windows(raw,starts,seq,device):return torch.from_numpy(np.stack([raw[i:i+seq] for i in starts])).to(device)
def prefix(model,tokens,stop,rotary):
 h=model.model.embed_tokens(tokens)
 for layer in model.model.layers[:stop]:h=forward_state(layer,h,rotary)
 return h

def nll_after(model,h,tokens,start,rotary,batch=8):
 losses=[]
 for lo in range(0,len(tokens),batch):
  z=h[lo:lo+batch]
  for layer in model.model.layers[start:]:z=forward_state(layer,z,rotary,batch)
  logits=model.lm_head(model.model.norm(z))
  v=F.cross_entropy(logits[:,:-1].float().reshape(-1,logits.shape[-1]),tokens[lo:lo+batch,1:].reshape(-1),reduction='none')
  losses.extend(v.reshape(len(z),-1).mean(-1).double().cpu().tolist())
 return losses

def native_losses(model,tokens,batch=8):
 losses=[]
 for lo in range(0,len(tokens),batch):
  chunk=tokens[lo:lo+batch]
  logits=model(input_ids=chunk,use_cache=False).logits
  v=F.cross_entropy(logits[:,:-1].float().reshape(-1,logits.shape[-1]),chunk[:,1:].reshape(-1),reduction='none')
  losses.extend(v.reshape(len(chunk),-1).mean(-1).double().cpu().tolist())
 return losses

def stats(losses,starts):
 assert len(losses)==len(starts) and all(math.isfinite(v) for v in losses)
 mean=st.mean(losses)
 return {'starts':starts,'sequence_nll':losses,'nll':mean,'ppl':math.exp(mean)}

def reset_student(teacher,student):
 student.load_state_dict(teacher.state_dict())
 for layer in student.model.layers:
  for n in NAMES:
   m=layer.get_submodule(n);m.weight.copy_(quantize(m.weight,4,128).to(m.weight.dtype))

def make_candidates(tlayer,slayer,fit_hidden,teacher_inputs,rotary,group,cfg):
 # No selection or audit input is accepted by this function.
 w={n:tlayer.get_submodule(n).weight.float() for n in group}
 _,inputs=capture_state(slayer,fit_hidden,rotary,[group[0]],cfg['microbatch'])
 x=teacher_inputs[group[0]].reshape(-1,w[group[0]].shape[1]);z=inputs[group[0]].reshape_as(x)
 fitted=fit_map(x,z,cfg['damping']);delta={n:correction(w[n],fitted) for n in group}
 candidates=[{n:quantize(w[n]+a*delta[n],cfg['bits'],cfg['group_size']).to(slayer.get_submodule(n).weight.dtype) for n in group} for a in cfg['alphas']]
 return candidates,fitted[2]

def install(layer,weights):
 for n,w in weights.items():layer.get_submodule(n).weight.copy_(w)

def audits(arrays,plan,cfg,device):
 seq=cfg['sequence_length'];out={}
 out['source']=(windows(arrays['train'],plan['source_audit_starts'],seq,device),plan['source_audit_starts'])
 for name,key in [('wiki','eval'),('novel','eval_extra')]:
  a,b=plan['audit_ranges'][key];starts=list(range(a,b,seq))
  out[name]=(windows(arrays[key],starts,seq,device),starts)
 return out

@torch.no_grad()
def run_path(teacher,student,arrays,fit_tokens,plan,cfg,policy,mode,draw,out,device):
 started=time.perf_counter();out.mkdir(parents=True,exist_ok=False)
 reset_student(teacher,student);seq=cfg['sequence_length'];L=len(teacher.model.layers);T=4*L
 rotary=teacher.model.rotary_emb(teacher.model.embed_tokens(fit_tokens),torch.arange(seq,device=device).unsqueeze(0))
 th=teacher.model.embed_tokens(fit_tokens);fh=th.clone()
 audit_tokens=windows(arrays['train'],plan['step_audit_starts'],seq,device)
 ah=student.model.embed_tokens(audit_tokens)
 adaptive=policy in ['task_select','local_select']
 if adaptive:
  draw_plan=plan['draws'][str(draw)];reuse_starts=draw_plan['reuse']
  reuse_tokens=windows(arrays['train'],reuse_starts,seq,device)
  sh=student.model.embed_tokens(reuse_tokens);tsh=teacher.model.embed_tokens(reuse_tokens)
 records=[];identity=[];first_hash=None
 for li,(tlayer,slayer) in enumerate(zip(teacher.model.layers,student.model.layers)):
  tn,tinputs=capture_state(tlayer,th,rotary,NAMES,cfg['microbatch'])
  for gi,group in enumerate(GROUPS):
   sync(device);step_start=time.perf_counter();step=li*4+gi
   if not adaptive:
    if policy=='qep_half':
     cands,ridge=make_candidates(tlayer,slayer,fh,tinputs,rotary,group,cfg);install(slayer,cands[1]);del cands
    rec={'step':step,'layer':li,'group':gi,'chosen_alpha':.5 if policy=='qep_half' else 0.}
   else:
    cands,ridge=make_candidates(tlayer,slayer,fh,tinputs,rotary,group,cfg)
    if step in [0,T//2,T-1]:
     again,_=make_candidates(tlayer,slayer,fh,tinputs,rotary,group,cfg)
     equal=all(torch.equal(a[n],b[n]) for a,b in zip(cands,again) for n in group)
     assert equal
     identity.append({'step':step,'same_fit_same_prefix_candidates_equal':equal})
     del again
    if step==0:first_hash=[{n:tensor_hash(c[n]) for n in group} for c in cands]
    if mode=='fresh':
     starts=draw_plan['fresh'][step];selected_tokens=windows(arrays['train'],starts,seq,device)
     hs=prefix(student,selected_tokens,li,rotary);ht=prefix(teacher,selected_tokens,li,rotary)
    else:starts=reuse_starts;selected_tokens=reuse_tokens;hs=sh;ht=tsh
    _,si=capture_state(slayer,hs,rotary,[group[0]],cfg['microbatch'])
    _,ti=capture_state(tlayer,ht,rotary,group,cfg['microbatch'])
    z=si[group[0]].float();targets={n:F.linear(ti[n].float(),tlayer.get_submodule(n).weight.float()) for n in group}
    candidates=[];prepared_at=time.perf_counter()
    for alpha,weights in zip(cfg['alphas'],cands):
     install(slayer,weights)
     errors=sum((F.linear(z,weights[n].float())-targets[n]).square().mean(dim=(1,2)) for n in group)
     h=forward_state(slayer,hs,rotary,cfg['microbatch'])
     losses=nll_after(student,h,selected_tokens,li+1,rotary,cfg['microbatch'])
     candidates.append({'alpha':alpha,'selection_nll':losses,'selection_mse':errors.double().cpu().tolist()})
    # Lock the action BEFORE obtaining audit losses. The selector has no audit argument.
    winner,scores=choose(policy,candidates);chosen=cfg['alphas'][winner]
    selected_at=time.perf_counter()
    for candidate,weights in zip(candidates,cands):
     install(slayer,weights)
     h=forward_state(slayer,ah,rotary,cfg['microbatch'])
     candidate['audit_nll']=nll_after(student,h,audit_tokens,li+1,rotary,cfg['microbatch'])
    install(slayer,cands[winner]);sync(device)
    rec={'step':step,'layer':li,'group':gi,'policy':policy,'mode':mode,'draw':draw,
         'selection_starts':starts,'audit_starts':plan['step_audit_starts'],'ridge':ridge,
         'candidates':candidates,'selector_scores':scores,'chosen_alpha':chosen,
         'seconds':time.perf_counter()-step_start,
         'preparation_seconds':prepared_at-step_start,'selection_scoring_seconds':selected_at-prepared_at,
         'audit_seconds':time.perf_counter()-selected_at}
    del cands,si,ti,z,targets,h,hs,ht,selected_tokens
   records.append(rec);append_json(out/'decisions.jsonl',rec)
  fh=forward_state(slayer,fh,rotary,cfg['microbatch']);th=tn
  ah=forward_state(slayer,ah,rotary,cfg['microbatch'])
  if adaptive and mode=='reuse':
   sh=forward_state(slayer,sh,rotary,cfg['microbatch']);tsh=forward_state(tlayer,tsh,rotary,cfg['microbatch'])
  del tinputs
  write_json(out/'progress.json',{'status':'running','completed_blocks':li+1,'total_blocks':L,'seconds':time.perf_counter()-started})
  if li%4==0 or li==L-1:print(json.dumps({'event':'block','path':out.name,'layer':li,'seconds':time.perf_counter()-started}),flush=True)
 constructed=time.perf_counter();final={}
 for name,(tokens,starts) in audits(arrays,plan,cfg,device).items():final[name]=stats(native_losses(student,tokens,cfg['microbatch']),starts)
 if adaptive and mode=='reuse':final['selection']=stats(native_losses(student,reuse_tokens,cfg['microbatch']),reuse_starts)
 elif adaptive:
  # Store final-policy per-window values, grouped by original decision, with NO pooled selection metric.
  for step,starts in enumerate(draw_plan['fresh']):
   tokens=windows(arrays['train'],starts,seq,device)
   append_json(out/'final_selection_windows.jsonl',{'step':step,'starts':starts,'sequence_nll':native_losses(student,tokens,cfg['microbatch'])})
 else:
  final['selection_by_draw']={}
  for d,v in plan['draws'].items():
   tokens=windows(arrays['train'],v['reuse'],seq,device)
   final['selection_by_draw'][d]=stats(native_losses(student,tokens,cfg['microbatch']),v['reuse'])
 verification={'same_prefix_checks':identity,'first_step_candidate_sha256':first_hash}
 if adaptive:
  # Same fixed audit subset telescopes along every path, even when selection windows change.
  first=next(c for c in records[0]['candidates'] if c['alpha']==0.)['audit_nll']
  last=next(c for c in records[-1]['candidates'] if c['alpha']==records[-1]['chosen_alpha'])['audit_nll']
  assert max(abs(a-b) for a,b in zip(last,final['source']['sequence_nll'][:cfg['step_audit_windows']]))<1e-5
  for prev,nxt in zip(records,records[1:]):
   before=next(c for c in prev['candidates'] if c['alpha']==prev['chosen_alpha'])
   zero=next(c for c in nxt['candidates'] if c['alpha']==0.)
   assert max(abs(a-b) for a,b in zip(before['audit_nll'],zero['audit_nll']))<1e-5
   if mode=='reuse':assert max(abs(a-b) for a,b in zip(before['selection_nll'],zero['selection_nll']))<1e-5
  verification['audit_telescope_final_max_error']=max(abs(a-b) for a,b in zip(last,final['source']['sequence_nll'][:8]))
 else:
  # Independent native masking/positions and then reconstruction from the recorded schedule.
  native_check={}
  for name,(tokens,starts) in audits(arrays,plan,cfg,device).items():
   manual=nll_after(student,student.model.embed_tokens(tokens),tokens,0,rotary,cfg['microbatch'])
   error=max(abs(a-b) for a,b in zip(manual,final[name]['sequence_nll']));assert error<1e-6
   native_check[name]={'manual_vs_native_max_error':error}
  reset_student(teacher,student)
  if policy=='qep_half':
   tx=teacher.model.embed_tokens(fit_tokens);sx=tx.clone()
   for li,(tl,sl) in enumerate(zip(teacher.model.layers,student.model.layers)):
    tx_next,inputs=capture_state(tl,tx,rotary,NAMES,cfg['microbatch'])
    for gi,g in enumerate(GROUPS):
     alpha=records[li*4+gi]['chosen_alpha'];assert alpha==.5
     weights={n:tl.get_submodule(n).weight.float() for n in g}
     _,captured=capture_state(sl,sx,rotary,[g[0]],cfg['microbatch'])
     x=inputs[g[0]].reshape(-1,weights[g[0]].shape[1]);z=captured[g[0]].reshape_as(x);fit=fit_map(x,z,cfg['damping'])
     for n in g:sl.get_submodule(n).weight.copy_(quantize(weights[n]+alpha*correction(weights[n],fit),4,128).to(sl.get_submodule(n).weight.dtype))
    sx=forward_state(sl,sx,rotary,cfg['microbatch']);tx=tx_next
  for name,(tokens,starts) in audits(arrays,plan,cfg,device).items():
   reconstructed=native_losses(student,tokens,cfg['microbatch'])
   error=max(abs(a-b) for a,b in zip(reconstructed,final[name]['sequence_nll']));assert error<1e-6
   native_check[name]['reconstructed_native_max_error']=error
  verification['native_reconstruction']=native_check
 sync(device)
 write_json(out/'verification.json',verification)
 write_json(out/'results.json',{'policy':policy,'mode':mode,'draw':draw,'model':plan['model'],'final':final,
            'construction_seconds':constructed-started,'total_seconds':time.perf_counter()-started,
            'fresh_selection_final_aggregation':'not defined; per-window records only' if mode=='fresh' else None})
 write_json(out/'progress.json',{'status':'complete','completed_blocks':L,'total_blocks':L,'seconds':time.perf_counter()-started})
 print(json.dumps({'event':'path_complete','path':out.name,'seconds':time.perf_counter()-started}),flush=True)
 return time.perf_counter()-started


def path_schedule():
 # First path is predeclared for timing; no outcome-dependent ordering.
 paths=[('task_select','reuse',1),('rtn','fixed',None),('qep_half','fixed',None)]
 paths += [(p,m,d) for d in [1,2] for m in ['reuse','fresh'] for p in ['task_select','local_select'] if (p,m,d)!=paths[0]]
 assert len(paths)==10
 return paths

@torch.no_grad()
def main():
 p=argparse.ArgumentParser();p.add_argument('--model-key',choices=['qwen3','llama3'],required=True);a=p.parse_args()
 freeze=checked_freeze();cfg=json.loads((ROOT/'configs/frozen.json').read_text());base=ROOT/'inputs'/a.model_key
 plan=json.loads((base/'plan.json').read_text());device='cuda:0'
 torch.set_num_threads(4);torch.manual_seed(2026101200);torch.backends.cuda.matmul.allow_tf32=False
 arrays={k:np.load(base/(k+'.npy'),mmap_mode='r') for k in ['train','eval','eval_extra']}
 for k,v in arrays.items():assert sha(v.tobytes())==plan['texts'][k]['token_sha256']
 fit_tokens=torch.from_numpy(np.load(base/'fit_tokens.npy')).to(device);assert tensor_hash(fit_tokens)==plan['fit_token_sha256']
 setup=time.perf_counter()
 teacher=AutoModelForCausalLM.from_pretrained(plan['checkpoint'],dtype=torch.bfloat16,attn_implementation='sdpa',local_files_only=True).to(device).eval()
 for v in teacher.parameters():v.requires_grad_(False)
 student=copy.deepcopy(teacher)
 out=ROOT/'results'/a.model_key;out.mkdir(parents=True,exist_ok=True)
 write_json(out/'manifest.json',{'frozen_sha256':freeze,'plan_sha256':sha((base/'plan.json').read_bytes()),'config':cfg,
          'torch':torch.__version__,'transformers':transformers.__version__,'gpu':torch.cuda.get_device_name(0),
          'visible_devices':os.environ.get('CUDA_VISIBLE_DEVICES'),'model_setup_seconds':time.perf_counter()-setup,
          'source_sha256':{f.name:sha(f.read_bytes()) for f in (ROOT/'src').glob('*.py')}})
 for i,(policy,mode,draw) in enumerate(path_schedule()):
  name=f'{policy}_{mode}'+(f'_draw{draw}' if draw is not None else '')
  dest=out/name
  if dest.exists():
   assert json.loads((dest/'progress.json').read_text())['status']=='complete','incomplete path requires explicit recovery'
   continue
  elapsed=run_path(teacher,student,arrays,fit_tokens,plan,cfg,policy,mode,draw,dest,device)
  if i==0:
   budget={'first_predeclared_path':name,'measured_seconds':elapsed,'remaining_paths_this_model':9,
           'conservative_remaining_seconds':elapsed*9*1.7,'method':'1.7x first path for remaining paths, allowing fresh prefixes and final per-window evaluation; timing only, no outcomes read',
           'protocol_sha256':sha((ROOT/'docs/specs/PROTOCOL.md').read_bytes())}
   write_json(ROOT/'verification'/f'budget_{a.model_key}.json',budget)
 write_json(out/'COMPLETE.json',{'paths':10,'status':'complete','frozen_sha256':freeze})
if __name__=='__main__':
 try:main()
 except Exception as e:
  print(json.dumps({'event':'failure','type':type(e).__name__,'message':str(e)}),flush=True)
  raise
