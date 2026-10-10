from pathlib import Path
import argparse,json,csv,hashlib,statistics as st,itertools

def assess(row,margin=1e-4):
 c=row['candidates'];a=min(range(len(c)),key=lambda i:c[i]['select']['rtn']);b=min(range(len(c)),key=lambda i:c[i]['select']['completed'])
 old_margin=c[b]['select']['rtn']-c[a]['select']['rtn']
 new_margin=c[a]['select']['completed']-c[b]['select']['completed']
 diag_old=c[b]['diag']['rtn']-c[a]['diag']['rtn'];diag_new=c[a]['diag']['completed']-c[b]['diag']['completed']
 inversions=sum((c[i]['select']['rtn']-c[j]['select']['rtn'])*(c[i]['select']['completed']-c[j]['select']['completed'])<0 and
   abs(c[i]['select']['rtn']-c[j]['select']['rtn'])>margin and abs(c[i]['select']['completed']-c[j]['select']['completed'])>margin
   for i,j in itertools.combinations(range(len(c)),2))
 robust=old_margin>margin and new_margin>margin
 return {'layer':row['layer'],'group':row['group'],'terminal_control':row['terminal_control'],
  'old_alpha':c[a]['alpha'],'new_alpha':c[b]['alpha'],'raw_switch':a!=b,'old_advantage':old_margin,
  'completed_regret':new_margin,'robust_switch':robust,'diagnostic_old_advantage':diag_old,
  'diagnostic_completed_gain':diag_new,'diagnostic_reversal':robust and diag_old>margin and diag_new>margin,
  'strict_pair_inversions':inversions}

def main(root):
 allrows=[];versions=set();counts=[]
 for model in ['qwen3','llama3']:
  for draw in [1,2]:
   p=root/f'{model}_draw{draw}';meta=json.loads((p/'manifest.json').read_text());checks=json.loads((p/'checks.json').read_text())
   assert json.loads((p/'progress.json').read_text())['status']=='complete'
   versions.add(tuple(sorted(meta['source_sha256'].items())))
   for name,digest in meta['source_sha256'].items():assert hashlib.sha256((p/name).read_bytes()).hexdigest()==digest
   assert checks['historical_candidate_comparisons']==96 and checks['terminal_comparisons']==24
   assert checks['historical_candidate_max_error']<1e-6 and checks['terminal_max_difference']==0
   raw=list(map(json.loads,(p/'interventions.jsonl').read_text().splitlines()));assert len(raw)==16
   for row in raw:
    out=assess(row);out.update(model=model,draw=draw);allrows.append(out)
   for margin in [1e-5,1e-4,1e-3]:
    v=[assess(x,margin) for x in raw if not x['terminal_control']];assert len(v)==12
    counts.append({'model':model,'draw':draw,'margin':margin,'groups':len(v),'raw_switches':sum(x['raw_switch'] for x in v),
      'robust_switches':sum(x['robust_switch'] for x in v),'diagnostic_reversals':sum(x['diagnostic_reversal'] for x in v),
      'strict_pair_inversions':sum(x['strict_pair_inversions'] for x in v),
      'mean_completed_regret':st.mean(x['completed_regret'] for x in v),'median_completed_regret':st.median(x['completed_regret'] for x in v),
      'max_completed_regret':max(x['completed_regret'] for x in v),'mean_diagnostic_completed_gain':st.mean(x['diagnostic_completed_gain'] for x in v)})
 assert len(versions)==1
 assert all(not x['raw_switch'] and x['completed_regret']==0 for x in allrows if x['terminal_control'])
 (root/'all_metrics.json').write_text(json.dumps(allrows,indent=2)+'\n');(root/'summary.json').write_text(json.dumps(counts,indent=2)+'\n')
 with (root/'all_metrics.csv').open('w') as f:
  w=csv.DictWriter(f,fieldnames=list(allrows[0]));w.writeheader();w.writerows(allrows)
 lines=['# Suffix intervention: fixed primary margin 1e-4 NLL','',
 '| Model | Draw | Nonterminal groups | Raw winner changes | Robust changes | Diagnostic reversals | Mean completed-suffix regret | Mean diagnostic gain |',
 '|---|---:|---:|---:|---:|---:|---:|---:|']
 for x in counts:
  if x['margin']==1e-4:lines.append(f"| {x['model']} | {x['draw']} | {x['groups']} | {x['raw_switches']} | {x['robust_switches']} | {x['diagnostic_reversals']} | {x['mean_completed_regret']:.7f} | {x['mean_diagnostic_completed_gain']:+.7f} |")
 lines+=['','Terminal blocks: 16 groups total, zero differences, no switches.','Historical candidate reproduction: 384 scores checked.','No simultaneous replacement or new full-policy performance measured.']
 (root/'SUMMARY.md').write_text('\n'.join(lines)+'\n');print('\n'.join(lines))

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--results',type=Path,default=Path(__file__).resolve().parents[1]/'results');a=p.parse_args();main(a.results)
