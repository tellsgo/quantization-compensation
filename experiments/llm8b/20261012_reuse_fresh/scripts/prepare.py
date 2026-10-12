"""Prepare input plans without loading model weights or observing model losses."""
from pathlib import Path
import argparse,hashlib,json
import numpy as np
from transformers import AutoTokenizer
ROOT=Path(__file__).resolve().parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def write(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def plan(train_count,steps,history,cfg):
 seq=cfg['sequence_length'];all_starts=np.arange(train_count//seq,dtype=np.int64)*seq
 fit=set(history['fit_starts']);diag=set(history['historical_diag_starts'])
 unseen=np.array([int(i) for i in all_starts if int(i) not in set(history['historical_train_starts'])])
 assert len(unseen)>=32
 audit=np.random.default_rng(cfg['audit_seed']).choice(unseen,32,replace=False).tolist()
 excluded=fit|diag|set(audit);pool=np.array([int(i) for i in all_starts if int(i) not in excluded])
 assert len(pool)>=steps*8,(len(pool),steps*8)
 draws={}
 for draw,seed in enumerate(cfg['selection_seeds'],1):
  fresh=np.random.default_rng(seed).choice(pool,steps*8,replace=False).reshape(steps,8).tolist()
  assert len(set(sum(fresh,[])))==steps*8 and not set(sum(fresh,[]))&excluded
  draws[str(draw)]={'seed':seed,'fresh':fresh,'reuse':fresh[0]}
 return {'fit_starts':sorted(fit),'source_audit_starts':audit,'step_audit_starts':audit[:8],
         'train_windows':len(all_starts),'audit_unseen_pool_windows':len(unseen),'selection_pool_windows':len(pool),
         'fresh_required_windows':steps*8,'historical_diag_excluded':sorted(diag),'draws':draws}
def main():
 p=argparse.ArgumentParser();p.add_argument('--models',required=True);p.add_argument('--data',required=True);a=p.parse_args()
 cfg=json.loads((ROOT/'configs/frozen.json').read_text());hist=json.loads((ROOT/'configs/history.json').read_text())
 for key,name in [('qwen3','Qwen3-8B'),('llama3','Meta-Llama-3-8B')]:
  out=ROOT/'inputs'/key;out.mkdir(parents=True,exist_ok=False)
  model=Path(a.models)/name;tokenizer=AutoTokenizer.from_pretrained(model,local_files_only=True)
  count=json.loads((model/'config.json').read_text())['num_hidden_layers'];steps=count*4
  arrays={};texts={}
  for split,f in [('train','wikitext2_train.txt'),('eval','wikitext2_test.txt'),('eval_extra','gutenberg_1342_body.txt')]:
   raw=(Path(a.data)/f).read_bytes();assert sha(raw)==hist[key]['text_sha256'][split]
   arrays[split]=np.asarray(tokenizer.encode(raw.decode(),add_special_tokens=False),dtype=np.int64)
   texts[split]={'text_sha256':sha(raw),'tokens':len(arrays[split]),'token_sha256':sha(arrays[split].tobytes())}
   np.save(out/(split+'.npy'),arrays[split])
  d=plan(len(arrays['train']),steps,hist[key],cfg)
  # Preserve historical fitting order, not only the fitting set.
  d['fit_starts']=hist[key]['fit_starts']
  fit=np.stack([arrays['train'][i:i+512] for i in d['fit_starts']]);assert sha(fit.tobytes())==hist[key]['fit_token_sha256']
  np.save(out/'fit_tokens.npy',fit)
  begin=cfg['evaluation_start'];end=begin+512*cfg['evaluation_windows']
  for split in ['eval','eval_extra']:
   assert len(arrays[split])>=end
   assert all(b<=begin or start>=end for start,b in hist[key]['evaluation_ranges'][split])
  d.update(model=key,checkpoint=str(model),layers=count,steps=steps,sequence_length=512,
           audit_ranges={'eval':[begin,end],'eval_extra':[begin,end]},texts=texts,
           fit_token_sha256=sha(fit.tobytes()),config_sha256=sha((ROOT/'configs/frozen.json').read_bytes()),
           checkpoint_config_sha256=sha((model/'config.json').read_bytes()),
           tokenizer_config_sha256=sha((model/'tokenizer_config.json').read_bytes()))
  write(out/'plan.json',d)
  print(json.dumps({'model':key,'layers':count,'train_windows':d['train_windows'],
    'selection_pool_windows':d['selection_pool_windows'],'fresh_required_windows':steps*8,
    'source_audit_never_previously_used':True,'evaluation_ranges':d['audit_ranges'],'text_tokens':{k:v['tokens'] for k,v in texts.items()}}),flush=True)
if __name__=='__main__':main()
