"""Portable diagnostic runner. Prepare public assets, freeze inputs, then capture and diagnose."""
from __future__ import annotations
import os
for key, value in {'HF_HUB_OFFLINE':'1','HF_HUB_DISABLE_IMPLICIT_TOKEN':'1','TOKENIZERS_PARALLELISM':'false',
                   'VECLIB_MAXIMUM_THREADS':'4','OMP_NUM_THREADS':'4','MKL_NUM_THREADS':'4'}.items():
    os.environ[key] = value
import argparse
import datetime
import hashlib
import importlib.metadata
import json
import platform
import re
import sys
import time
from pathlib import Path
import numpy as np
import torch
import pyarrow.parquet as pq
from safetensors import safe_open
from transformers import AutoTokenizer, AutoModelForCausalLM
from c6_core import scales, derived_seed, encode_decode, correction, audit, prepare_accounting, prepare_baseline

ROOT = Path(__file__).resolve().parent
MODELS = {
 'smol135': {'repo':'HuggingFaceTB/SmolLM2-135M','rev':'93efa2f097d58c2a74874c7e644dbc9b0cee75a2','prefix':'model.layers.','layers':210},
 'pythia160': {'repo':'EleutherAI/pythia-160m','rev':'50f5173d932e8e61f858120bcb800b97af589f46','prefix':'gpt_neox.layers.','layers':48}}
OLD_CACHE = Path(os.environ.get('HF_HUB_CACHE', str(Path.home() / '.cache/huggingface/hub')))
SEEDS = list(range(2026100400,2026100416))
ALPHAS = [.5,1.]


def sha(path):
    h=hashlib.sha256()
    with open(path,'rb') as f:
        for block in iter(lambda:f.read(8*1024*1024),b''):h.update(block)
    return h.hexdigest()


def write(path, obj):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(obj,indent=2,ensure_ascii=False,allow_nan=False)+'\n')


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def modelpath(model):
    m=MODELS[model]
    return OLD_CACHE/('models--'+m['repo'].replace('/','--'))/'snapshots'/m['rev']


def prepare():
    """Materials, tokenizer arrays, and safetensors module inventory only."""
    manifest={'created_at':now(),'host':platform.node(),'python':sys.version,'models':{},'tokens':{},'packages':{}}
    for name in ['torch','numpy','transformers','pyarrow','safetensors','huggingface_hub','psutil']:
        manifest['packages'][name]=importlib.metadata.version(name)
    public=ROOT/'public_sources'
    raw=(public/'gutenberg_1342.txt').read_text(encoding='utf-8-sig')
    start=re.search(r'^\*\*\* START OF THE PROJECT GUTENBERG EBOOK[^\n]*\*\*\*\s*$',raw,re.M)
    end=re.search(r'^\*\*\* END OF THE PROJECT GUTENBERG EBOOK[^\n]*\*\*\*\s*$',raw,re.M)
    if not start or not end or end.start()<=start.end():raise ValueError('standard Gutenberg wrapper missing')
    gutenberg=raw[start.end():end.start()].strip()
    wiki={split:'\n\n'.join(t for t in pq.read_table(public/f'wikitext2_{split}.parquet')['text'].to_pylist() if t.strip())
          for split in ['train','validation']}
    manifest['source_files']=[{'name':p.name,'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(public.iterdir()) if p.suffix in ['.txt','.parquet']]
    for model,m in MODELS.items():
        p=modelpath(model)
        files=[{'name':f.name,'sha256':sha(f),'bytes':f.stat().st_size} for f in sorted(p.iterdir()) if f.is_file()]
        modules=[]
        with safe_open(str(p/'model.safetensors'),framework='np') as sf:
            for key in sorted(sf.keys()):
                if key.startswith(m['prefix']) and key.endswith('.weight'):
                    shape=sf.get_slice(key).get_shape()
                    if len(shape)==2:modules.append({'name':key[:-7],'shape':shape,'block':int(key[len(m['prefix']):].split('.')[0])})
        if len(modules)!=m['layers']:raise ValueError('unexpected module count')
        manifest['models'][model]={**m,'path':str(p),'files':files,'modules':modules}
        tok=AutoTokenizer.from_pretrained(p,local_files_only=True,token=False)
        for dataset in ['wikitext','gutenberg']:
            if dataset=='wikitext':
                train=tok.encode(wiki['train'],add_special_tokens=False)
                val=tok.encode(wiki['validation'],add_special_tokens=False)
                arrays={'cal':np.asarray(train[:4096],dtype=np.int64).reshape(32,128),
                        'holdout':np.asarray(val[:2048],dtype=np.int64).reshape(16,128)}
                offsets={'cal':[0,4096],'holdout':[0,2048],'holdout_source':'validation'}
            else:
                data=tok.encode(gutenberg,add_special_tokens=False)
                arrays={'cal':np.asarray(data[:4096],dtype=np.int64).reshape(32,128),
                        'holdout':np.asarray(data[8192:10240],dtype=np.int64).reshape(16,128)}
                offsets={'cal':[0,4096],'holdout':[8192,10240],'holdout_source':'same_book_after_4096_token_gap'}
            key=f'{model}_{dataset}'
            manifest['tokens'][key]={'offsets':offsets,'files':{}}
            for split,array in arrays.items():
                path=ROOT/'tokens'/f'{key}_{split}.npy';path.parent.mkdir(exist_ok=True)
                np.save(path,array,allow_pickle=False)
                manifest['tokens'][key]['files'][split]={'path':str(path.relative_to(ROOT)),'shape':list(array.shape),'sha256':sha(path),'token_bytes_sha256':hashlib.sha256(array.tobytes()).hexdigest()}
    manifest['settings']={'alphas':ALPHAS,'seeds':SEEDS,'cpu_threads':4,'inference_dtype':'float32','accounting_dtype':'float64','device':'cpu','attention':'eager','rcond':1e-10}
    write(ROOT/'prepared_manifest.json',manifest)
    write(ROOT/'FROZEN_MANIFEST.json', {'sha256':{name:sha(ROOT/name) for name in ['c6_core.py','c6_run.py','prepared_manifest.json']}})
    print(json.dumps({'phase':'prepare','status':'prepared_no_model_forward','manifest_sha256':sha(ROOT/'prepared_manifest.json')}),flush=True)


def verify_lock():
    lock=json.loads((ROOT/'FROZEN_MANIFEST.json').read_text())
    for relative,hashvalue in lock['sha256'].items():
        if sha(ROOT/relative)!=hashvalue:raise RuntimeError('frozen file changed: '+relative)
    prepared=json.loads((ROOT/'prepared_manifest.json').read_text())
    for model,m in prepared['models'].items():
        for f in m['files']:
            if sha(Path(m['path'])/f['name'])!=f['sha256']:raise RuntimeError('model/tokenizer file changed')
    return prepared


def capture(modelkey, dataset, prepared):
    """One teacher and one uncorrected deterministic BASE trajectory; never QEP rollout."""
    torch.set_num_threads(4)
    torch.set_num_interop_threads(1)
    torch.use_deterministic_algorithms(True)
    meta=prepared['models'][modelkey]
    cell=ROOT/'runs'/f'{modelkey}_{dataset}';cell.mkdir(parents=True,exist_ok=True)
    tokens=np.concatenate([np.load(ROOT/prepared['tokens'][f'{modelkey}_{dataset}']['files'][s]['path'],allow_pickle=False) for s in ['cal','holdout']],axis=0)
    model=AutoModelForCausalLM.from_pretrained(meta['path'],local_files_only=True,token=False,dtype=torch.float32,attn_implementation='eager').eval()
    mods=dict(model.named_modules())
    if not all(isinstance(mods[m['name']],torch.nn.Linear) for m in meta['modules']):raise RuntimeError('module inventory differs from loaded model')
    for m in meta['modules']:
        folder=cell/m['name'];folder.mkdir(exist_ok=True)
        np.save(folder/'weight.npy',mods[m['name']].weight.detach().cpu().numpy(),allow_pickle=False)
    for trajectory in ['teacher','base']:
        if trajectory=='base':
            for m in meta['modules']:
                folder=cell/m['name'];w=np.load(folder/'weight.npy',allow_pickle=False).astype(np.float64)
                q,_=encode_decode(w,scales(w),folder/'upstream_det_packet.npz')
                with torch.no_grad():mods[m['name']].weight.copy_(torch.from_numpy(q.astype(np.float32)))
        arrays={};counters={};hooks=[]
        for m in meta['modules']:
            name=m['name'];arrays[name]=np.lib.format.open_memmap(cell/name/f'{trajectory}_inputs.npy',mode='w+',dtype=np.float32,shape=(6144,m['shape'][1]));counters[name]=0
            def make_hook(name):
                def hook(module,args):
                    x=args[0].detach().cpu().numpy().reshape(-1,args[0].shape[-1])
                    i=counters[name];arrays[name][i:i+len(x)]=x;counters[name]+=len(x)
                return hook
            hooks.append(mods[name].register_forward_pre_hook(make_hook(name)))
        with torch.inference_mode():
            for seq_index,seq in enumerate(tokens):
                ids=torch.from_numpy(seq[None,:].copy())
                # Base model avoids retaining vocabulary logits; all Transformer inputs unchanged.
                if trajectory=='teacher' and seq_index==0:
                    marker={'event':'first_model_forward_immediately_next','time':now(),'model':modelkey,'dataset':dataset,
                            'frozen_manifest_sha256':sha(ROOT/'FROZEN_MANIFEST.json'),'pid':os.getpid()}
                    write(cell/'first_forward.json',marker)
                    if not (ROOT/'FIRST_FORWARD.json').exists():write(ROOT/'FIRST_FORWARD.json',marker)
                    print(json.dumps(marker),flush=True)
                model.base_model(input_ids=ids,use_cache=False,return_dict=False)
        for h in hooks:h.remove()
        for name,a in arrays.items():
            if counters[name]!=6144:raise RuntimeError('missing activation rows '+name)
            a.flush()
        del arrays
        print(json.dumps({'phase':'capture','model':modelkey,'dataset':dataset,'trajectory':trajectory,'time':now()}),flush=True)
    del model
    records=[]
    for m in meta['modules']:
        folder=cell/m['name']
        records.append({'module':m['name'],'files':{name:{'sha256':sha(folder/name),'bytes':(folder/name).stat().st_size} for name in ['weight.npy','teacher_inputs.npy','base_inputs.npy','upstream_det_packet.npz']}})
    write(cell/'capture_manifest.json',{'records':records,'time':now()})


def diagnose(modelkey,dataset,prepared):
    cell=ROOT/'runs'/f'{modelkey}_{dataset}';output=cell/'layer_statistics.jsonl'
    if output.exists():raise RuntimeError('existing diagnostic output must not be overwritten')
    with output.open('x') as stream:
        for module in prepared['models'][modelkey]['modules']:
            name=module['name'];folder=cell/name;t0=time.monotonic()
            w=np.load(folder/'weight.npy',allow_pickle=False).astype(np.float64)
            xall=np.load(folder/'teacher_inputs.npy',mmap_mode='r',allow_pickle=False)
            zall=np.load(folder/'base_inputs.npy',mmap_mode='r',allow_pickle=False)
            x=xall[:4096].T.astype(np.float64);z=zall[:4096].T.astype(np.float64)
            try:
                c,project=correction(w,x,z)
                np.save(folder/'correction.npy',c,allow_pickle=False)
                delta=scales(w)
                xh=xall[4096:].T.astype(np.float64);zh=zall[4096:].T.astype(np.float64)
                contexts=[prepare_accounting(w,c,x,z),prepare_accounting(w,c,xh,zh)]
                for mode,seed in [('deterministic',None)]+[('subtractive_dither',seed) for seed in SEEDS]:
                    ds=None if seed is None else derived_seed(MODELS[modelkey]['repo'],name,seed)
                    tag='det' if seed is None else f'dither_{seed}'
                    q0,packet0=encode_decode(w,delta,folder/'packets'/f'{tag}_a0.npz',ds)
                    baselines=[prepare_baseline(w,q0,z,contexts[0]),prepare_baseline(w,q0,zh,contexts[1])]
                    for alpha in ALPHAS:
                        qa,packeta=encode_decode(w+alpha*c,delta,folder/'packets'/f'{tag}_a{alpha}.npz',ds)
                        row={'model':modelkey,'dataset':dataset,'module':name,'block':module['block'],'shape':list(w.shape),
                             'mode':mode,'seed':seed,'alpha':alpha,'projection':project,'packets':[packet0,packeta],
                             'zero_weight_rows':int((np.max(np.abs(w),axis=1)==0).sum())}
                        row['cal']=audit(w,c,q0,qa,x,z,alpha,True,contexts[0],baselines[0])
                        row['holdout']=audit(w,c,q0,qa,xh,zh,alpha,False,contexts[1],baselines[1])
                        row['quality_pass']=project['projection_quality_pass'] and row['cal']['accounting_quality_pass'] and row['holdout']['accounting_quality_pass']
                        stream.write(json.dumps(row,allow_nan=False)+'\n');stream.flush()
            except Exception as error:
                stream.write(json.dumps({'model':modelkey,'dataset':dataset,'module':name,'quality_pass':False,'error':type(error).__name__+': '+str(error)})+'\n');stream.flush()
                raise
            print(json.dumps({'phase':'diagnose','model':modelkey,'dataset':dataset,'module':name,'seconds':time.monotonic()-t0,'time':now()}),flush=True)
    write(cell/'execution_status.json',{'status':'AWAITING_REVIEW','ended':now(),'statistics_sha256':sha(output),
          'rows_expected':len(prepared['models'][modelkey]['modules'])*34,'rows_actual':sum(1 for _ in output.open()),
          'cache_includes_full_activations_and_packets':True,'not_a_portable_complete_bundle':True})


def main():
    p=argparse.ArgumentParser();p.add_argument('phase',choices=['prepare','capture','diagnose']);p.add_argument('--model',choices=MODELS);p.add_argument('--dataset',choices=['wikitext','gutenberg']);a=p.parse_args()
    if a.phase=='prepare':prepare();return
    if a.model is None or a.dataset is None:raise ValueError('model and dataset required')
    prepared=verify_lock()
    print(json.dumps({'phase':a.phase,'started':now(),'host':platform.node(),'frozen_sha256':sha(ROOT/'FROZEN_MANIFEST.json')}),flush=True)
    (capture if a.phase=='capture' else diagnose)(a.model,a.dataset,prepared)

if __name__=='__main__':main()
