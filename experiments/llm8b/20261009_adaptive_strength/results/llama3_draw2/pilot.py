"""Actual-codebook slice test of a frozen-rounding-error coefficient proposal."""
from pathlib import Path
import argparse,copy,json,time,hashlib,os,statistics
import numpy as np
import torch
import torch.nn.functional as F
import transformers
from transformers import AutoModelForCausalLM
from core import GROUPS,quantize,fit_map,correction,write_json
from scale_selection import forward_state,capture_state,append_json
from proposal import coefficient,neighbor,choose

def sync():torch.cuda.synchronize()
def timed(fn):
 sync();t=time.perf_counter();v=fn();sync();return v,time.perf_counter()-t

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def nll_of_hidden(model,h,tokens):
 logits=model.lm_head(model.model.norm(h))
 return float(F.cross_entropy(logits[:,:-1].float().reshape(-1,logits.shape[-1]),tokens[:,1:].reshape(-1)))

@torch.no_grad()
def main(a):
 out=Path(a.output);out.mkdir(parents=True,exist_ok=False);base=Path(a.base);cfg=json.loads(Path(a.config).read_text());start=time.time()
 meta=json.loads((base/'manifest.json').read_text());data=json.loads((base/'data.json').read_text())
 torch.set_num_threads(4);torch.backends.cuda.matmul.allow_tf32=False;torch.manual_seed(meta['config']['seed'])
 sources={}
 for n in ['pilot.py','proposal.py','core.py','scale_selection.py']:
  f=Path(__file__).with_name(n);sources[n]=sha(f);(out/n).write_bytes(f.read_bytes())
 for n in ['core.py','scale_selection.py']:assert sources[n]==meta['source_sha256'][n]
 protocol=Path(__file__).parents[1]/'docs/specs/RUN_PROTOCOL.md';(out/'RUN_PROTOCOL.md').write_bytes(protocol.read_bytes())
 write_json(out/'manifest.json',{'config':cfg,'args':vars(a),'parent_manifest_sha256':sha(base/'manifest.json'),'source_sha256':sources,
 'protocol_sha256':sha(protocol),'torch':torch.__version__,'transformers':transformers.__version__,'gpu':torch.cuda.get_device_name(0),'seed':meta['config']['seed'],'start_unix':start})
 (out/'parent_manifest.json').write_bytes((base/'manifest.json').read_bytes());write_json(out/'data.json',data)
 tokens={}
 for k in ['cal','select','diag']:
  v=np.load(base/f'{k}_tokens.npy');assert hashlib.sha256(v.tobytes()).hexdigest()==data['token_hashes'][k]
  np.save(out/f'{k}_tokens.npy',v);tokens[k]=torch.from_numpy(v).cuda()
 model=AutoModelForCausalLM.from_pretrained(meta['args']['model'],dtype=torch.bfloat16,attn_implementation='sdpa',local_files_only=True).cuda().eval()
 for p in model.parameters():p.requires_grad_(False)
 layers=model.model.layers;rtn=copy.deepcopy(layers);names=sum(GROUPS,[]);L=len(layers)
 for layer in rtn:
  for n in names:
   m=layer.get_submodule(n);m.weight.copy_(quantize(m.weight,cfg['bits'],128))
 ts={k:model.model.embed_tokens(v) for k,v in tokens.items()};ss={k:v.clone() for k,v in ts.items()}
 rotary=model.model.rotary_emb(ts['cal'],torch.arange(512,device='cuda').unsqueeze(0))
 # Independent parent-model call validates native decoder masking/positions and RTN decomposition.
 parity={};tiny=tokens['select'][:1]
 for label,ll in [('teacher',layers),('rtn',rtn)]:
  h=model.model.embed_tokens(tiny)
  for layer in ll:h=forward_state(layer,h,rotary)
  manual=nll_of_hidden(model,h,tiny);model.model.layers=ll
  logits=model(input_ids=tiny,use_cache=False).logits
  native=float(F.cross_entropy(logits[:,:-1].float().reshape(-1,logits.shape[-1]),tiny[:,1:].reshape(-1)))
  assert abs(manual-native)<1e-6,(label,manual,native);parity[label]={'manual':manual,'native':native,'difference':abs(manual-native)}
 model.model.layers=layers;write_json(out/'native_parity.json',parity)
 audited={1,L//2,L-2};count=0
 for li,(teacher,student) in enumerate(zip(layers,rtn)):
  if li in audited:
   for gi,group in enumerate(GROUPS):
    sync();common_start=time.perf_counter()
    w={n:teacher.get_submodule(n).weight.float().clone() for n in group}
    _,tf=capture_state(teacher,ts['cal'],rotary,[group[0]]);_,sf=capture_state(student,ss['cal'],rotary,[group[0]])
    x=tf[group[0]].reshape(-1,w[group[0]].shape[1]);z=sf[group[0]].reshape_as(x);fit=fit_map(x,z,cfg['damping'])
    delta={n:correction(w[n],fit) for n in group};ridge=fit[2];del tf,sf,x,z,fit
    _,tselect=capture_state(teacher,ts['select'],rotary,group);_,sselect=capture_state(student,ss['select'],rotary,[group[0]])
    zs=sselect[group[0]].float();targets={n:F.linear(tselect[n].float(),w[n]) for n in group};del tselect,sselect
    q0={n:quantize(w[n],2,128).to(torch.bfloat16) for n in group}
    assert all(torch.equal(q0[n],student.get_submodule(n).weight) for n in group)
    energy=sum(float(t.square().mean()) for t in targets.values());assert energy>0
    baseline=sum(float((targets[n]-F.linear(zs,q0[n].float())).square().mean()) for n in group)
    sync();common_seconds=time.perf_counter()-common_start
    def estimate():
     dot=den=0.
     for n in group:
      residual=targets[n]-F.linear(zs,q0[n].float());direction=F.linear(zs,delta[n])
      dot+=float((residual*direction).mean());den+=float(direction.square().mean())
     alpha,degenerate=coefficient(dot,den,energy,cfg['degenerate_relative'])
     return {'alpha':alpha,'degenerate':degenerate,'dot':dot,'direction_energy':den}
    est,est_seconds=timed(estimate);alpha=est['alpha'];near=neighbor(alpha,cfg['neighbor_step'])
    rng=np.random.default_rng(meta['config']['seed']+100000*cfg['bits']+100*li+gi);randoms=rng.uniform(0,1,2).tolist()
    def loss_at(v,zinput=zs,target=targets):
     return sum(float((target[n]-F.linear(zinput,quantize(w[n]+v*delta[n],2,128).to(torch.bfloat16).float())).square().mean()) for n in group)
    def search(points):
     scores=[{'alpha':0.,'loss':baseline}]
     for v in sorted(set(points)-{0.}):scores.append({'alpha':v,'loss':loss_at(v)})
     return {'winner':choose(scores),'scores':scores}
    def theory_search():
     estimate_now=estimate();assert estimate_now['alpha']==alpha
     return search([alpha,near])
    methods={'theory2':theory_search,'grid10':lambda:search(cfg['grid']),'fixed2':lambda:search([.5,1.]),'random2':lambda:search(randoms)}
    # Equal warmup before measured repetitions, followed by rotated order.
    for fn in methods.values():fn()
    timings={k:[] for k in methods};selections={}
    for repeat in range(cfg['timing_repeats']):
     order=list(methods);shift=(li+gi+repeat)%len(order);order=order[shift:]+order[:shift]
     for name in order:
      answer,seconds=timed(methods[name]);timings[name].append(seconds);selections[name]=answer
    chosen={'zero':0.,'half':.5,'full':1.,'center':alpha,'random1':randoms[0]}
    chosen.update({k:v['winner']['alpha'] for k,v in selections.items()})
    # Entire diagnostic/metadata pass is excluded from coefficient-selection timing.
    _,td=capture_state(teacher,ts['diag'],rotary,group);_,sd=capture_state(student,ss['diag'],rotary,[group[0]])
    zd=sd[group[0]].float();targetd={n:F.linear(td[n].float(),w[n]) for n in group};del td,sd
    energyd=sum(float(t.square().mean()) for t in targetd.values());assert energyd>0
    points=sorted(set([0.,.5,1.,alpha,near]+cfg['grid']+randoms));curve=[]
    basecodes={n:quantize(w[n],2,128,True)[1:] for n in group}
    for v in points:
     sel=loss_at(v);diag=loss_at(v,zd,targetd)
     counts={'weights':0,'changed_codes':0,'groups':0,'changed_scales':0,'changed_zero_points':0}
     for n in group:
      q,code,scale,zero=quantize(w[n]+v*delta[n],2,128,True);assert int(code.min())>=0 and int(code.max())<=3
      bc,bs,bz=basecodes[n];counts['weights']+=code.numel();counts['changed_codes']+=int((code!=bc).sum());counts['groups']+=scale.numel()
      counts['changed_scales']+=int((scale!=bs).sum());counts['changed_zero_points']+=int((zero!=bz).sum())
     curve.append({'alpha':v,'select_loss':sel,'diag_loss':diag,'frozen_prediction':baseline-2*v*est['dot']+v*v*est['direction_energy'],'code_changes':counts})
    assert abs(curve[0]['select_loss']-baseline)<=1e-6*max(1.,baseline)
    outcomes={name:next(c for c in curve if c['alpha']==v) for name,v in chosen.items()}
    for name,answer in selections.items():assert abs(outcomes[name]['select_loss']-answer['winner']['loss'])<=1e-6*max(1.,baseline)
    for n in group:assert torch.equal(q0[n],student.get_submodule(n).weight)
    append_json(out/'slices.jsonl',{'layer':li,'group':gi,'group_names':group,'estimate':est,'ridge':ridge,'target_energy':{'select':energy,'diag':energyd},
       'outcomes':outcomes,'curve':curve,'common_seconds':common_seconds,'estimate_seconds':est_seconds,'timings':timings,
       'median_incremental_seconds':{k:statistics.median(v) for k,v in timings.items()},
       'scored_candidate_counts':{k:len(v['scores'])-1 for k,v in selections.items()}})
    count+=1;print(json.dumps({'event':'slice_complete','layer':li,'group':gi,'count':count}),flush=True)
    del w,delta,zs,targets,q0,zd,targetd,basecodes,curve,outcomes
  for k in tokens:
   ts[k]=forward_state(teacher,ts[k],rotary);ss[k]=forward_state(student,ss[k],rotary)
 assert count==12
 write_json(out/'progress.json',{'status':'complete','slices':count,'wall_seconds':time.time()-start})
 print(json.dumps({'event':'complete','wall_seconds':time.time()-start}),flush=True)

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--base',required=True);p.add_argument('--output',required=True);p.add_argument('--config',required=True);a=p.parse_args()
 try:main(a)
 except Exception as e:
  if Path(a.output).exists():write_json(Path(a.output)/'failure.json',{'type':type(e).__name__,'message':str(e)})
  raise
