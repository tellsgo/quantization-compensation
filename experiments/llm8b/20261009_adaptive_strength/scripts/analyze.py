from pathlib import Path
import argparse,json,csv,math,statistics as st,hashlib

def ranks(a):
 out=[0.]*len(a);order=sorted(range(len(a)),key=lambda i:a[i]);i=0
 while i<len(a):
  j=i+1
  while j<len(a) and a[order[j]]==a[order[i]]:j+=1
  for k in range(i,j):out[order[k]]=(i+j-1)/2
  i=j
 return out

def spearman(a,b):
 a=ranks(a);b=ranks(b);ma=st.mean(a);mb=st.mean(b)
 n=sum((x-ma)*(y-mb) for x,y in zip(a,b));d=math.sqrt(sum((x-ma)**2 for x in a)*sum((y-mb)**2 for y in b))
 return n/d if d else None

def main(root):
 rows=[];summaries=[];source_versions=set();protocols=set()
 methods=['zero','half','full','center','random1','theory2','grid10','fixed2','random2']
 for model in ['qwen3','llama3']:
  for draw in [1,2]:
   p=root/f'{model}_draw{draw}';meta=json.loads((p/'manifest.json').read_text());cfg=meta['config']
   assert json.loads((p/'progress.json').read_text())['status']=='complete'
   source_versions.add(tuple(sorted(meta['source_sha256'].items())));protocols.add(meta['protocol_sha256'])
   for name,digest in meta['source_sha256'].items():assert hashlib.sha256((p/name).read_bytes()).hexdigest()==digest
   assert hashlib.sha256((p/'RUN_PROTOCOL.md').read_bytes()).hexdigest()==meta['protocol_sha256']
   raw=[json.loads(line) for line in (p/'slices.jsonl').read_text().splitlines()];assert len(raw)==12
   curves=[];local=[]
   for s in raw:
    fixed=[c for c in s['curve'] if c['alpha'] in [0.]+cfg['grid']];assert len(fixed)==11
    corr=spearman([c['frozen_prediction'] for c in fixed],[c['select_loss'] for c in fixed]);curves.append(corr)
    o=s['outcomes'];energy=s['target_energy'];zero=o['zero'];half=o['half']
    for method in methods:
     q=o[method]
     for split in ['select','diag']:
      val=q[split+'_loss']/energy[split];base=zero[split+'_loss']/energy[split];h=half[split+'_loss']/energy[split]
      assert all(math.isfinite(x) for x in [val,base,h])
      row={'model':model,'draw':draw,'layer':s['layer'],'group':s['group'],'method':method,'split':split,'alpha':q['alpha'],
        'normalized_residual':val,'gain_vs_zero':base-val,'difference_vs_half':val-h,'harm_vs_zero':val>base+1e-8*max(1.,abs(base)),
        'harm_vs_half':val>h+1e-8*max(1.,abs(h)),'grid_regret':val-o['grid10'][split+'_loss']/energy[split]}
      rows.append(row);local.append(row)
    for method in ['theory2','grid10','fixed2','random2']:
     assert len(s['timings'][method])==3
     assert abs(s['median_incremental_seconds'][method]-st.median(s['timings'][method]))<1e-12
    for method in ['grid10','theory2','fixed2','random2']:
     assert o[method]['select_loss']<=zero['select_loss']+1e-7*max(1.,zero['select_loss'])
   mean=lambda method,split:st.mean(x['normalized_residual'] for x in local if x['method']==method and x['split']==split)
   gain=lambda method,split:sum(x['gain_vs_zero'] for x in local if x['method']==method and x['split']==split)
   common=sum(x['common_seconds'] for x in raw)
   cost={m:sum(s['median_incremental_seconds'][m] for s in raw) for m in ['theory2','grid10','fixed2','random2']}
   condition={'model':model,'draw':draw,'center_alpha_min':min(x['estimate']['alpha'] for x in raw),
     'center_alpha_median':st.median(x['estimate']['alpha'] for x in raw),'center_alpha_max':max(x['estimate']['alpha'] for x in raw),
     'center_at_one':sum(x['estimate']['alpha']==1 for x in raw),'degenerate':sum(x['estimate']['degenerate'] for x in raw),
     'spearman_mean':st.mean(x for x in curves if x is not None) if any(x is not None for x in curves) else None,
     'spearman_all':curves,'means':{m:{k:mean(m,k) for k in ['select','diag']} for m in methods},
     'common_seconds':common,'incremental_seconds':cost,'total_seconds':{m:common+c for m,c in cost.items()},
     'theory_to_grid_incremental_ratio':cost['theory2']/cost['grid10'],
     'theory_to_grid_total_ratio':(common+cost['theory2'])/(common+cost['grid10']),
     'retained_gain':{k:(gain('theory2',k)/gain('grid10',k) if gain('grid10',k)>1e-12 else None) for k in ['select','diag']},
     'harm_counts':{m:{k:sum(x['harm_vs_zero'] for x in local if x['method']==m and x['split']==k) for k in ['select','diag']} for m in methods}}
   condition['gate1']=all(mean('center',k)<mean(m,k) for k in ['select','diag'] for m in ['half','random1'])
   condition['gate2']=condition['theory_to_grid_total_ratio']<=.2 and all(v is not None and v>=.9 for v in condition['retained_gain'].values())
   condition['gate3']=mean('theory2','diag')<mean('grid10','diag') and condition['harm_counts']['theory2']['diag']<=condition['harm_counts']['grid10']['diag']
   summaries.append(condition)
 assert len(source_versions)==1 and len(protocols)==1
 with (root/'all_metrics.csv').open('w') as f:
  w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
 (root/'all_metrics.json').write_text(json.dumps(rows,indent=2)+'\n');(root/'summary.json').write_text(json.dumps(summaries,indent=2)+'\n')
 lines=['# Adaptive strength first-stage results','',
 '| Model | Draw | Center at 1 /12 | Mean curve rank correlation | Theory/grid total time | Select gain retained | Diagnostic gain retained | Gates 1/2/3 |',
 '|---|---:|---:|---:|---:|---:|---:|---|']
 def ratio(v):return 'undefined' if v is None else f'{v:.3f}'
 for x in summaries:lines.append(f"| {x['model']} | {x['draw']} | {x['center_at_one']} | {ratio(x['spearman_mean'])} | {ratio(x['theory_to_grid_total_ratio'])} | {ratio(x['retained_gain']['select'])} | {ratio(x['retained_gain']['diag'])} | {x['gate1']}/{x['gate2']}/{x['gate3']} |")
 lines+=['','Gate1: standalone center beats half/random1 on both splits in each condition. Gate2: <=20% measured common-inclusive decision time and >=90% dense residual gain on both splits. Gate3: theory2 improves diagnostic mean and has no greater harm count than grid.','',
 'Measurements are correlated slices on fixed RTN trajectories, not independent model runs or complete-policy results.']
 (root/'SUMMARY.md').write_text('\n'.join(lines)+'\n');print('\n'.join(lines))

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--results',type=Path,default=Path(__file__).resolve().parents[1]/'results');a=p.parse_args();main(a.results)
