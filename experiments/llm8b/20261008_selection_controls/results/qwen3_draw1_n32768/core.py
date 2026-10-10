"""Real-codebook QEP decision pilot. No claims of packed inference or universal guarantees."""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
import math
import os
from pathlib import Path
import time

import numpy as np
import torch
import torch.nn.functional as F
import transformers
from transformers import AutoModelForCausalLM, AutoTokenizer

GROUPS = [
    ['self_attn.q_proj', 'self_attn.k_proj', 'self_attn.v_proj'],
    ['self_attn.o_proj'],
    ['mlp.gate_proj', 'mlp.up_proj'],
    ['mlp.down_proj'],
]
POLICIES = ['rtn', 'qep_half', 'qep_no_down', 'local_select', 'lookahead_select']


def sha(b):
    return hashlib.sha256(b).hexdigest()


def write_json(path, obj):
    path = Path(path)
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(obj, ensure_ascii=False, indent=2, allow_nan=False) + '\n')
    tmp.replace(path)


def quantize(w, bits=4, group_size=128, return_codes=False):
    """Per-row asymmetric groups, integer codes, dequantize into original shape."""
    assert w.ndim == 2 and w.shape[1] % group_size == 0
    z = w.float().reshape(w.shape[0], -1, group_size)
    levels = 2**bits - 1
    lo = torch.minimum(z.amin(-1, keepdim=True), torch.zeros_like(z[..., :1]))
    hi = torch.maximum(z.amax(-1, keepdim=True), torch.zeros_like(z[..., :1]))
    scale = ((hi - lo) / levels).clamp_min(torch.finfo(torch.float32).tiny)
    zero = torch.round(-lo / scale).clamp(0, levels)
    code = torch.round(z / scale + zero).clamp(0, levels)
    q = ((code - zero) * scale).reshape_as(w)
    assert torch.isfinite(q).all()
    if return_codes:
        return q, code.to(torch.uint8), scale, zero
    return q


def fit_map(x, z, damping):
    """Return K with W_corrected = W + alpha * W @ K; X,Z are token x feature."""
    x, z = x.float(), z.float()
    n, d = z.shape
    assert x.shape == z.shape and damping > 0
    lam = damping * z.square().sum() / d
    lam = lam.clamp_min(1e-12)
    drift = x - z
    if n < d:
        gram = z @ z.T
        gram.diagonal().add_(lam)
        chol = torch.linalg.cholesky(gram)
        # Keep factors instead of materializing a d-by-d correction map.
        solved = torch.cholesky_solve(z, chol)
        return drift.T, solved, float(lam)
    gram = z.T @ z
    gram.diagonal().add_(lam)
    chol = torch.linalg.cholesky(gram)
    cross = drift.T @ z
    k = torch.cholesky_solve(cross.T, chol).T
    return k, None, float(lam)


def correction(w, fit):
    a, b, _ = fit
    return w.float() @ a if b is None else (w.float() @ a) @ b


def block_forward(layer, h, rotary):
    out = layer(h, position_embeddings=rotary, use_cache=False)
    return out[0] if isinstance(out, tuple) else out


def capture(layer, h, rotary, names):
    inputs = {}
    handles = []
    for name in names:
        def hook(module, args, name=name):
            inputs[name] = args[0].detach()
        handles.append(layer.get_submodule(name).register_forward_pre_hook(hook))
    try:
        out = block_forward(layer, h, rotary)
    finally:
        for handle in handles:
            handle.remove()
    assert set(inputs) == set(names)
    return out, inputs


def mse(a, b):
    return float((a.float() - b.float()).square().mean())


def make_tokens(tokenizer, train_path, eval_path, cfg, device):
    train_bytes, eval_bytes = train_path.read_bytes(), eval_path.read_bytes()
    train = tokenizer.encode(train_bytes.decode(), add_special_tokens=False)
    evaluation = tokenizer.encode(eval_bytes.decode(), add_special_tokens=False)
    seq = cfg['sequence_length']
    ncal, nsel, ntest = (cfg[k] for k in ['calibration_tokens','selection_tokens','evaluation_tokens'])
    assert all(n % seq == 0 for n in [ncal,nsel,ntest])
    # Explicit disjoint raw token ranges in the train split. Gap is not a generalization guarantee.
    offsets = {'cal':[0,ncal], 'select':[ncal+8192,ncal+8192+nsel], 'eval':[0,ntest]}
    assert len(train) >= offsets['select'][1] and len(evaluation) >= ntest
    arrays = {}
    for split,(start,end) in offsets.items():
        raw = evaluation if split == 'eval' else train
        arrays[split] = np.array(raw[start:end],dtype=np.int64).reshape(-1,seq)
    assert not (set(map(tuple,arrays['cal'])) & set(map(tuple,arrays['select'])))
    meta = {'train_text_sha256':sha(train_bytes),'evaluation_text_sha256':sha(eval_bytes),
            'offsets':offsets,'tokenizer':str(tokenizer.name_or_path),
            'token_hashes':{k:sha(v.tobytes()) for k,v in arrays.items()},
            'decoded_prefixes':{k:tokenizer.decode(v.ravel()[:80].tolist()) for k,v in arrays.items()}}
    return {k:torch.from_numpy(v).to(device) for k,v in arrays.items()},meta


def nll(model, hidden, tokens):
    losses=[]
    for i in range(len(tokens)):
        logits = model.lm_head(model.model.norm(hidden[i:i+1]))
        value = F.cross_entropy(logits[:,:-1,:].float().reshape(-1,logits.shape[-1]),
                                tokens[i:i+1,1:].reshape(-1),reduction='mean')
        losses.append(float(value))
    mean = sum(losses)/len(losses)
    return {'nll':mean,'ppl':math.exp(mean),'sequence_nll':losses,
            'scored_tokens':int(len(tokens)*(tokens.shape[1]-1))}


@torch.inference_mode()
def run(args):
    out = Path(args.output)
    out.mkdir(parents=True,exist_ok=False)
    cfg = json.loads(Path(args.config).read_text())
    policies = cfg.get('policies',POLICIES)
    assert all(p in POLICIES for p in policies)
    device = torch.device('cuda:0')
    torch.set_num_threads(4)
    torch.manual_seed(cfg['seed'])
    torch.backends.cuda.matmul.allow_tf32=False
    source = Path(__file__).read_bytes()
    manifest={'config':cfg,'model':args.model,'source_sha256':sha(source),
              'torch':torch.__version__,'transformers':transformers.__version__,
              'cuda_visible_devices':os.environ.get('CUDA_VISIBLE_DEVICES'),
              'gpu':torch.cuda.get_device_name(0),'start_unix':time.time(),
              'execution':'BF16 dequantized weights from integer codebooks; not packed inference'}
    write_json(out/'manifest.json',manifest)
    tokenizer=AutoTokenizer.from_pretrained(args.model,local_files_only=True)
    tok,data_meta=make_tokens(tokenizer,Path(args.train),Path(args.evaluation),cfg,device)
    write_json(out/'data.json',data_meta)
    for name,value in tok.items(): np.save(out/f'{name}_tokens.npy',value.cpu().numpy())
    print(json.dumps({'event':'data_checked','prefix':data_meta['decoded_prefixes']['cal']}),flush=True)
    model=AutoModelForCausalLM.from_pretrained(args.model,dtype=torch.bfloat16,
                                             attn_implementation='sdpa',local_files_only=True).to(device).eval()
    for p in model.parameters():p.requires_grad_(False)
    assert model.config.model_type in ['qwen3','llama']
    teacher={s:model.model.embed_tokens(t) for s,t in tok.items()}
    states={p:{s:h.clone() for s,h in teacher.items()} for p in policies}
    pos=torch.arange(cfg['sequence_length'],device=device).unsqueeze(0)
    rotary=model.model.rotary_emb(teacher['cal'],pos)
    names=sum(GROUPS,[])
    policy_time={p:0. for p in policies}
    records=[]
    block_count=len(model.model.layers)
    # No test metric is computed until all selection decisions have been made.
    for li,layer in enumerate(model.model.layers):
        started=time.time()
        weights={name:layer.get_submodule(name).weight.detach().float().clone() for name in names}
        rtn={name:quantize(w,cfg['bits'],cfg['group_size']).to(torch.bfloat16) for name,w in weights.items()}
        teacher_out, teacher_cal=capture(layer,teacher['cal'],rotary,names)
        teacher_sel_out, teacher_sel=capture(layer,teacher['select'],rotary,names)
        teacher_eval_out=block_forward(layer,teacher['eval'],rotary)
        future=None
        if 'lookahead_select' in policies and li+1<block_count:
            next_orig=model.model.layers[li+1]
            teacher_future=block_forward(next_orig,teacher_sel_out,rotary)
            future=copy.deepcopy(next_orig)
            for name in names:
                mod=future.get_submodule(name)
                mod.weight.copy_(quantize(mod.weight,cfg['bits'],cfg['group_size']).to(mod.weight.dtype))
        else:
            teacher_future=model.model.norm(teacher_sel_out)
        for policy in policies:
            pstart=time.time()
            for name in names:layer.get_submodule(name).weight.copy_(rtn[name])
            choices=[]
            for gi,group in enumerate(GROUPS):
                if policy=='rtn' or (policy=='qep_no_down' and gi==3):
                    choices.append({'group':gi,'alpha':0.,'scores':None});continue
                _,scal=capture(layer,states[policy]['cal'],rotary,[group[0]])
                x=teacher_cal[group[0]].reshape(-1,weights[group[0]].shape[1])
                z=scal[group[0]].reshape_as(x)
                fit=fit_map(x,z,cfg['damping'])
                delta={name:correction(weights[name],fit) for name in group}
                selecting=policy.endswith('_select')
                alphas=cfg['candidate_strengths'] if selecting else [.5]
                if policy=='local_select':
                    _,ssel=capture(layer,states[policy]['select'],rotary,[group[0]])
                    zsel=ssel[group[0]].float()
                    targets={name:F.linear(teacher_sel[name].float(),weights[name]) for name in group}
                scores=[];best=None;best_score=float('inf');best_alpha=None
                for alpha in alphas:
                    candidates={name:quantize(weights[name]+alpha*delta[name],cfg['bits'],cfg['group_size']).to(torch.bfloat16)
                                for name in group}
                    if policy=='local_select':
                        score=sum(mse(F.linear(zsel,candidates[name].float()),targets[name]) for name in group)
                    elif policy=='lookahead_select':
                        for name in group:layer.get_submodule(name).weight.copy_(candidates[name])
                        h=block_forward(layer,states[policy]['select'],rotary)
                        pred=block_forward(future,h,rotary) if future is not None else model.model.norm(h)
                        score=mse(pred,teacher_future)
                    else:score=0.
                    assert math.isfinite(score)
                    scores.append({'alpha':alpha,'score':score})
                    if score<best_score:
                        best_score=score;best=candidates;best_alpha=alpha
                for name in group:layer.get_submodule(name).weight.copy_(best[name])
                choices.append({'group':gi,'alpha':best_alpha,'scores':scores,'ridge':fit[2],
                                'drift_relative':float(torch.linalg.vector_norm(x.float()-z.float())/
                                                       torch.linalg.vector_norm(x.float()).clamp_min(1e-12))})
                del fit,delta,scal
            for split in states[policy]:states[policy][split]=block_forward(layer,states[policy][split],rotary)
            torch.cuda.synchronize()
            policy_time[policy]+=time.time()-pstart
            rec={'layer':li,'policy':policy,'choices':choices,'seconds_cumulative':policy_time[policy]}
            records.append(rec)
            with (out/'decisions.jsonl').open('a') as f:f.write(json.dumps(rec,allow_nan=False)+'\n')
        teacher={'cal':teacher_out,'select':teacher_sel_out,'eval':teacher_eval_out}
        del weights,rtn,teacher_cal,teacher_sel,future
        write_json(out/'progress.json',{'completed_blocks':li+1,'total_blocks':block_count,'status':'running',
                                        'seconds_this_block':time.time()-started})
        print(json.dumps({'event':'block_done','block':li,'seconds':time.time()-started}),flush=True)
    results={'teacher':nll(model,teacher['eval'],tok['eval']), 'policies':{},
             'policy_construction_seconds':policy_time,'end_unix':time.time()}
    for policy in policies:
        results['policies'][policy]=nll(model,states[policy]['eval'],tok['eval'])
        results['policies'][policy]['hidden_relative_mse']=float(
            (states[policy]['eval'].float()-teacher['eval'].float()).square().sum()/
            teacher['eval'].float().square().sum())
    write_json(out/'results.json',results)
    write_json(out/'progress.json',{'completed_blocks':block_count,'total_blocks':block_count,'status':'complete'})
    print(json.dumps({'event':'complete','results':results}),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    for key in ['model','train','evaluation','config','output']:parser.add_argument('--'+key,required=True)
    args=parser.parse_args()
    try:run(args)
    except Exception as exc:
        if Path(args.output).is_dir():
            write_json(Path(args.output)/'failure.json',{'type':type(exc).__name__,'message':str(exc)})
        raise
