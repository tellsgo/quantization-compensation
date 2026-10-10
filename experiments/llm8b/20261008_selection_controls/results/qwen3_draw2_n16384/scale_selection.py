"""Nested selection-size experiment. Diagnostics never enter decisions."""
from pathlib import Path
import argparse
import copy
import json
import os
import time
import numpy as np
import torch
import torch.nn.functional as F
import transformers
from transformers import AutoModelForCausalLM, AutoTokenizer
from core import GROUPS, quantize, fit_map, correction, block_forward, capture, mse, nll, sha, write_json

POLICIES=['rtn','local_select','block_select','task_select']


def forward_state(layer,h,rotary,batch=8):
    return torch.cat([block_forward(layer,h[i:i+batch],rotary) for i in range(0,len(h),batch)])


def capture_state(layer,h,rotary,names,batch=8):
    chunks=[capture(layer,h[i:i+batch],rotary,names) for i in range(0,len(h),batch)]
    inputs={};shared={}
    for name in names:
        key=tuple((v[name].data_ptr(),tuple(v[name].shape),tuple(v[name].stride())) for _,v in chunks)
        if key not in shared:shared[key]=torch.cat([v[name] for _,v in chunks])
        inputs[name]=shared[key]
    return torch.cat([v for v,_ in chunks]),inputs


def nested_windows(train, base_cal, base_select, seed, sequence=512, maximum=32768, diagnostic=8192):
    """Input ranges are aligned block starts; size cannot change the sampled pool."""
    used=list(base_cal)+list(base_select)
    assert all(i%sequence==0 for i in used) and len(set(used))==len(used)
    assert len(base_cal)==4 and len(base_select)==8
    available=np.setdiff1d(np.arange(len(train)//sequence)*sequence,np.array(used))
    rng=np.random.default_rng(seed+910000)
    extra=rng.choice(available,size=maximum//sequence-len(base_select)+diagnostic//sequence,replace=False)
    selection=list(base_select)+extra[:maximum//sequence-len(base_select)].tolist()
    diag=extra[maximum//sequence-len(base_select):].tolist()
    starts={'cal':list(base_cal),'select':selection,'diag':diag}
    assert not(set(selection)&set(diag) or set(base_cal)&set(selection) or set(base_cal)&set(diag))
    arrays={k:np.stack([np.asarray(train[i:i+sequence],dtype=np.int64) for i in v]) for k,v in starts.items()}
    return arrays,starts


def load_tokens(tokenizer,args,cfg,device):
    train_bytes=Path(args.train).read_bytes()
    train=tokenizer.encode(train_bytes.decode(),add_special_tokens=False)
    base=Path(args.base_run)
    old=json.loads((base/'data.json').read_text())
    assert json.loads((base/'manifest.json').read_text())['config']['seed']==cfg['seed']
    assert sha(train_bytes)==old['train_text_sha256']
    cal=[a for a,b in old['offsets']['cal']]
    sel=[a for a,b in old['offsets']['select']]
    arrays,starts=nested_windows(train,cal,sel,cfg['seed'])
    assert np.array_equal(arrays['cal'],np.load(base/'cal_tokens.npy'))
    assert np.array_equal(arrays['select'][:8],np.load(base/'select_tokens.npy'))
    maximum_hash=sha(arrays['select'].tobytes())
    arrays['select']=arrays['select'][:cfg['selection_tokens']//512]
    starts['select']=starts['select'][:cfg['selection_tokens']//512]
    hashes={'train':sha(train_bytes)}
    for split,path in [('eval',args.evaluation),('eval_extra',args.extra)]:
        raw=Path(path).read_bytes();ids=tokenizer.encode(raw.decode(),add_special_tokens=False)
        begin=cfg['evaluation_start'];end=begin+cfg['evaluation_tokens']
        assert len(ids)>=end
        arrays[split]=np.asarray(ids[begin:end],dtype=np.int64).reshape(-1,512)
        starts[split]=list(range(begin,end,512));hashes[split]=sha(raw)
    # Additional exact-token duplicate guard, not a guarantee of document independence.
    train_sets={k:set(map(tuple,arrays[k])) for k in ['cal','select','diag']}
    for a,b in [('cal','select'),('cal','diag'),('select','diag')]:
        assert not train_sets[a]&train_sets[b],(a,b)
    meta={'source_hashes':hashes,'starts':starts,'maximum_selection_sha256':maximum_hash,
          'token_hashes':{k:sha(v.tobytes()) for k,v in arrays.items()},'base_run':str(base),
          'decoded_prefixes':{k:tokenizer.decode(v[0,:40].tolist()) for k,v in arrays.items()}}
    return {k:torch.from_numpy(v).to(device) for k,v in arrays.items()},meta


def suffix_value(model,layers,rotary,h,tokens,start,batch=8,gradient=False):
    """Mean next-token NLL; optional correctly weighted gradient, bounded graph memory."""
    values=[];grads=[];total=len(tokens)
    for lo in range(0,total,batch):
        hi=min(lo+batch,total)
        with torch.set_grad_enabled(gradient):
            v=h[lo:hi].detach().clone().requires_grad_(gradient)
            z=v
            for layer in layers[start:]:z=block_forward(layer,z,rotary)
            logits=model.lm_head(model.model.norm(z))
            losses=F.cross_entropy(logits[:,:-1].float().reshape(-1,logits.shape[-1]),
                tokens[lo:hi,1:].reshape(-1),reduction='none').reshape(hi-lo,-1).mean(-1)
            if gradient:
                g=torch.autograd.grad(losses.sum()/total,v)[0]
                grads.append(g.detach().float())
            values.extend(losses.detach().double().cpu().tolist())
        del v,z,logits,losses
    value=sum(values)/len(values)
    return (value,torch.cat(grads)) if gradient else value


def append_json(path,value):
    with path.open('a') as f:f.write(json.dumps(value,allow_nan=False)+'\n')


@torch.no_grad()
def run(args):
    out=Path(args.output);out.mkdir(parents=True,exist_ok=False)
    cfg=json.loads(Path(args.config).read_text())
    assert cfg['selection_tokens'] in [4096,16384,32768] and cfg['microbatch']==8
    for key,value in {'bits':4,'group_size':128,'damping':1.,'sequence_length':512,
                      'calibration_tokens':2048,'diagnostic_tokens':8192,
                      'candidate_strengths':[0.,.5,1.]}.items():assert cfg[key]==value,(key,cfg[key])
    torch.set_num_threads(4);torch.manual_seed(cfg['seed']);torch.backends.cuda.matmul.allow_tf32=False
    device='cuda:0';started=time.time()
    sources={}
    for name in ['scale_selection.py','core.py']:
        raw=Path(__file__).with_name(name).read_bytes();sources[name]=sha(raw);(out/name).write_bytes(raw)
    write_json(out/'manifest.json',{'config':cfg,'args':vars(args),'source_sha256':sources,
        'torch':torch.__version__,'transformers':transformers.__version__,'gpu':torch.cuda.get_device_name(0),
        'cuda_visible_devices':os.environ.get('CUDA_VISIBLE_DEVICES'),'start_unix':started})
    write_json(out/'config.json',cfg)
    tokenizer=AutoTokenizer.from_pretrained(args.model,local_files_only=True)
    tok,data_meta=load_tokens(tokenizer,args,cfg,device);write_json(out/'data.json',data_meta)
    for k,v in tok.items():np.save(out/f'{k}_tokens.npy',v.cpu().numpy())
    model=AutoModelForCausalLM.from_pretrained(args.model,dtype=torch.bfloat16,
        attn_implementation='sdpa',local_files_only=True).to(device).eval()
    for p in model.parameters():p.requires_grad_(False)
    names=sum(GROUPS,[]);layers=model.model.layers;count=len(layers)
    frozen=copy.deepcopy(layers)
    for layer in frozen:
        for name in names:
            mod=layer.get_submodule(name);mod.weight.copy_(quantize(mod.weight,4,128).to(mod.weight.dtype))
    teacher={k:model.model.embed_tokens(v) for k,v in tok.items()}
    states={p:{k:v.clone() for k,v in teacher.items()} for p in POLICIES}
    rotary=model.model.rotary_emb(teacher['cal'],torch.arange(512,device=device).unsqueeze(0))
    audit_layers={0,count//3,2*count//3,count-1}
    times={p:0. for p in POLICIES};previous_task=None
    for li,layer in enumerate(layers):
        tic=time.time()
        weights={n:layer.get_submodule(n).weight.float().clone() for n in names}
        rtn={n:quantize(w,4,128).to(torch.bfloat16) for n,w in weights.items()}
        tcal,ical=capture_state(layer,teacher['cal'],rotary,names)
        tsel,isel=capture_state(layer,teacher['select'],rotary,names)
        next_teacher={'cal':tcal,'select':tsel}
        for k in ['diag','eval','eval_extra']:next_teacher[k]=forward_state(layer,teacher[k],rotary)
        for policy in POLICIES:
            pstart=time.time()
            for n in names:layer.get_submodule(n).weight.copy_(rtn[n])
            choices=[]
            for gi,group in enumerate(GROUPS):
                if policy=='rtn':choices.append({'group':gi,'alpha':0.});continue
                _,scal=capture_state(layer,states[policy]['cal'],rotary,[group[0]])
                x=ical[group[0]].reshape(-1,weights[group[0]].shape[1]);z=scal[group[0]].reshape_as(x)
                fit=fit_map(x,z,1.);delta={n:correction(weights[n],fit) for n in group}
                audit=policy=='task_select' and cfg['selection_tokens']==4096 and li in audit_layers
                need_local=policy=='local_select' or audit
                if need_local:
                    _,ssel=capture_state(layer,states[policy]['select'],rotary,[group[0]])
                    zsel=ssel[group[0]].float()
                    target={n:F.linear(isel[n].float(),weights[n]) for n in group}
                direction_base=direction_grad=None
                if audit:
                    direction_base=forward_state(layer,states[policy]['select'],rotary)
                    _,direction_grad=suffix_value(model,frozen,rotary,direction_base,tok['select'],li+1,cfg['microbatch'],True)
                candidates_log=[];best=None;best_score=float('inf');best_alpha=None
                for alpha in [0.,.5,1.]:
                    candidate={n:quantize(weights[n]+alpha*delta[n],4,128).to(torch.bfloat16) for n in group}
                    local_score=sum(mse(F.linear(zsel,candidate[n].float()),target[n]) for n in group) if need_local else None
                    h=None;block_score=task_score=None
                    if policy!='local_select' or audit:
                        for n in group:layer.get_submodule(n).weight.copy_(candidate[n])
                        h=forward_state(layer,states[policy]['select'],rotary)
                        block_score=mse(h,tsel)
                    if policy=='task_select':
                        task_score=suffix_value(model,frozen,rotary,h,tok['select'],li+1,cfg['microbatch'])
                    score={'local_select':local_score,'block_select':block_score,'task_select':task_score}[policy]
                    assert np.isfinite(score)
                    row={'alpha':alpha,'score':score}
                    if audit:
                        hd=forward_state(layer,states[policy]['diag'],rotary)
                        row.update(local_mse=local_score,block_mse=block_score,task_nll=task_score,
                            directional=float(((h.float()-direction_base.float())*direction_grad).sum()),
                            diagnostic_nll=suffix_value(model,frozen,rotary,hd,tok['diag'],li+1,cfg['microbatch']))
                    candidates_log.append(row)
                    # Deliberately score-only: diagnostic fields are never used here.
                    if score<best_score:best_score=score;best=candidate;best_alpha=alpha
                if policy=='task_select':
                    assert best_score<=candidates_log[0]['score']+1e-8
                    if previous_task is not None:
                        assert abs(candidates_log[0]['score']-previous_task)<1e-5,(li,gi,previous_task,candidates_log[0])
                    previous_task=best_score
                for n in group:layer.get_submodule(n).weight.copy_(best[n])
                choices.append({'group':gi,'alpha':best_alpha,'scores':candidates_log,'ridge':fit[2]})
                if audit:append_json(out/'matched_state.jsonl',{'layer':li,'group':gi,'trajectory':policy,'candidates':candidates_log})
                del fit,delta,scal,direction_base,direction_grad
                if need_local:del ssel,zsel,target
            for k in states[policy]:states[policy][k]=forward_state(layer,states[policy][k],rotary)
            torch.cuda.synchronize();times[policy]+=time.time()-pstart
            append_json(out/'decisions.jsonl',{'layer':li,'policy':policy,'choices':choices,'seconds_cumulative':times[policy]})
            if li in audit_layers:
                checkpoints={k:suffix_value(model,frozen,rotary,states[policy][k],tok[k],li+1,cfg['microbatch']) for k in ['select','diag']}
                append_json(out/'trajectory.jsonl',{'layer':li,'policy':policy,**checkpoints})
        teacher=next_teacher
        del weights,rtn,ical,isel
        write_json(out/'progress.json',{'status':'running','completed_blocks':li+1,'total_blocks':count,'seconds_this_block':time.time()-tic})
        print(json.dumps({'event':'block','layer':li,'seconds':time.time()-tic}),flush=True)
    results={'teacher':{},'policies':{},'policy_construction_seconds':times,'wall_seconds':time.time()-started}
    for split in ['select','diag','eval','eval_extra']:
        results['teacher'][split]=nll(model,teacher[split],tok[split])
    for policy in POLICIES:
        results['policies'][policy]={k:nll(model,states[policy][k],tok[k]) for k in ['select','diag','eval','eval_extra']}
    write_json(out/'results.json',results)
    write_json(out/'progress.json',{'status':'complete','completed_blocks':count,'total_blocks':count})
    print(json.dumps({'event':'complete','wall_seconds':results['wall_seconds']}),flush=True)


if __name__=='__main__':
    ap=argparse.ArgumentParser()
    for key in ['model','train','evaluation','extra','base-run','config','output']:ap.add_argument('--'+key,required=True)
    args=ap.parse_args()
    try:run(args)
    except Exception as exc:
        if Path(args.output).is_dir():write_json(Path(args.output)/'failure.json',{'type':type(exc).__name__,'message':str(exc)})
        raise
