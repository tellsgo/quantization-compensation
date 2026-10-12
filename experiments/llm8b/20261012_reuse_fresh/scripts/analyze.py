"""Recompute every reported scalar from frozen plans and per-window observations."""
from pathlib import Path
import argparse,csv,hashlib,json,math,statistics as st,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
from design import choose,step_optimism

def obj(p):return json.loads(p.read_text())
def rows(p):return [json.loads(s) for s in p.read_text().splitlines() if s.strip()]
def mean_metric(v):
 x=st.mean(v['sequence_nll']);assert abs(x-v['nll'])<1e-12 and abs(math.exp(x)-v['ppl'])<1e-10
 assert len(v['starts'])==len(v['sequence_nll'])
 return x

def main():
 cfg=obj(ROOT/'configs/frozen.json');all_rows=[];decisions=0;identities=0;p4=[];verifications=[];predictions={}
 for model in ['qwen3','llama3']:
  plan=obj(ROOT/'inputs'/model/'plan.json');base=ROOT/'results'/model
  assert obj(base/'COMPLETE.json')['paths']==10
  rtn=obj(base/'rtn_fixed/results.json')['final']
  for v in [rtn['source'],rtn['wiki'],rtn['novel'],*rtn['selection_by_draw'].values()]:mean_metric(v)
  first_hashes=[];lookup={}
  for path in sorted(base.iterdir()):
   if not path.is_dir():continue
   r=obj(path/'results.json');v=obj(path/'verification.json');records=rows(path/'decisions.jsonl')
   assert obj(path/'progress.json')['status']=='complete' and len(records)==plan['steps']
   final=r['final'];p=r['policy'];mode=r['mode'];draw=r['draw']
   for key in ['source','wiki','novel']:mean_metric(final[key])
   item={'model':model,'policy':p,'mode':mode,'draw':draw,
      **{f'{k}_nll':mean_metric(final[k]) for k in ['source','wiki','novel']},
      'source_gain_vs_rtn':rtn['source']['nll']-final['source']['nll'],
      'selection_nll':None,'step_selection_gain':None,'step_audit_gain':None,'step_optimism':None,
      'path_optimism_audit8':None,'path_optimism_source32':None,
      'construction_seconds':r['construction_seconds'],'total_seconds':r['total_seconds']}
   if mode=='fixed':
    for value in final['selection_by_draw'].values():mean_metric(value)
    for domain,checks in v['native_reconstruction'].items():
     assert checks['manual_vs_native_max_error']<1e-6 and checks['reconstructed_native_max_error']<1e-6
     verifications.append({'model':model,'policy':p,'domain':domain,**checks})
   else:
    identities+=len(v['same_prefix_checks']);assert len(v['same_prefix_checks'])==3
    assert all(x['same_fit_same_prefix_candidates_equal'] for x in v['same_prefix_checks'])
    first_hashes.append(v['first_step_candidate_sha256']);gains=[];max_continuity=0.
    for step,record in enumerate(records):
     assert record['step']==step and len(record['candidates'])==3
     expected=plan['draws'][str(draw)]['reuse'] if mode=='reuse' else plan['draws'][str(draw)]['fresh'][step]
     assert record['selection_starts']==expected and record['audit_starts']==plan['step_audit_starts']
     cs=record['candidates'];assert [c['alpha'] for c in cs]==cfg['alphas']
     for c in cs:
      for f in ['selection_nll','selection_mse','audit_nll']:
       assert len(c[f])==8 and all(math.isfinite(x) for x in c[f])
     winner,scores=choose(p,cs)
     assert cs[winner]['alpha']==record['chosen_alpha'] and scores==record['selector_scores']
     if p=='task_select':assert scores[winner]<=scores[0]+1e-12
     if step:
      prev=records[step-1];chosen=next(c for c in prev['candidates'] if c['alpha']==prev['chosen_alpha'])
      fields=['audit_nll']+(['selection_nll'] if mode=='reuse' else [])
      for field in fields:max_continuity=max(max_continuity,max(abs(a-b) for a,b in zip(chosen[field],cs[0][field])))
     gains.append(step_optimism(record));decisions+=1
    assert max_continuity<1e-5
    sg=sum(g['selection_gain'] for g in gains);ag=sum(g['audit_gain'] for g in gains);op=sg-ag
    audit_final_gain=st.mean(rtn['source']['sequence_nll'][:8])-st.mean(final['source']['sequence_nll'][:8])
    assert abs(ag-audit_final_gain)<1e-5
    item.update(step_selection_gain=sg,step_audit_gain=ag,step_optimism=op)
    if mode=='reuse':
     loss=mean_metric(final['selection']);base_loss=rtn['selection_by_draw'][str(draw)]['nll']
     assert final['selection']['starts']==plan['draws'][str(draw)]['reuse']
     assert abs(sg-(base_loss-loss))<1e-5
     item.update(selection_nll=loss,path_optimism_audit8=base_loss-loss-audit_final_gain,
                 path_optimism_source32=base_loss-loss-item['source_gain_vs_rtn'])
     assert abs(item['path_optimism_audit8']-op)<1e-5
    else:
     assert 'selection' not in final
     selection=rows(path/'final_selection_windows.jsonl');assert len(selection)==plan['steps']
     for step,row in enumerate(selection):
      assert row['step']==step and row['starts']==plan['draws'][str(draw)]['fresh'][step]
      assert len(row['sequence_nll'])==8 and all(math.isfinite(x) for x in row['sequence_nll'])
    lookup[p,mode,draw]=item
   all_rows.append(item)
  assert len(first_hashes)==8 and all(h==first_hashes[0] for h in first_hashes)
  summaries={}
  for p in ['task_select','local_select']:
   for mode in ['reuse','fresh']:
    rr=[lookup[p,mode,d] for d in [1,2]]
    summaries[p,mode]={'step':st.mean(x['step_optimism'] for x in rr),
     'path32':st.mean(x['path_optimism_source32'] for x in rr) if mode=='reuse' else None,
     'source':st.mean(x['source_nll'] for x in rr)}
  net=summaries['task_select','reuse'];local=summaries['local_select','reuse']
  nf=summaries['task_select','fresh'];lf=summaries['local_select','fresh']
  lo,hi=cfg['p1_network_range']
  p1_positive=net['path32']>0
  p1=lo<=net['path32']<=hi and abs(local['path32'])<=cfg['p1_local_abs_max']
  p2_network=net['step']>0 and nf['step']<=cfg['p2_network_max_ratio']*net['step']
  p2_local=abs(lf['step']-local['step'])<=cfg['p2_local_max_change']
  p3=nf['source']<=net['source']
  predictions[model]={'P1':p1,'P1_network_positive':p1_positive,'P1_network_optimism_source32':net['path32'],
      'P1_local_optimism_source32':local['path32'],'P2':p2_network and p2_local,
      'P2_network':p2_network,'P2_local':p2_local,'network_reuse_step_optimism':net['step'],
      'network_fresh_step_optimism':nf['step'],'fresh_over_reuse':nf['step']/net['step'] if net['step']>0 else None,
      'local_step_change':lf['step']-local['step'],'P3':p3,'network_fresh_minus_reuse_source_nll':nf['source']-net['source']}
  adopted=[]
  for draw in [1,2]:
   a=lookup['task_select','reuse',draw];b=lookup['local_select','reuse',draw]
   gain=b['selection_nll']-a['selection_nll'];adopt=gain>cfg['threshold'];audit_gain=b['source_nll']-a['source_nll']
   selected=a if adopt else b
   p4.append({'model':model,'draw':draw,'selection_gain_network_over_local':gain,'threshold':cfg['threshold'],
       'adopt_network':adopt,'predicted_adoption':model=='qwen3','source_gain_network_over_local':audit_gain,
       'correct_on_source_audit':audit_gain>=0 if adopt else audit_gain<=0,
       **{f'rule_{k}_nll':selected[f'{k}_nll'] for k in ['source','wiki','novel']}})
   adopted.append(adopt==(model=='qwen3'))
  predictions[model]['P4']=all(adopted)
 assert decisions==2176 and identities==48,(decisions,identities)
 out=ROOT/'results'
 with (out/'all_metrics.csv').open('w') as f:
  w=csv.DictWriter(f,fieldnames=list(all_rows[0]));w.writeheader();w.writerows(all_rows)
 summary={'predictions':predictions,'threshold_rule':p4,'paths':all_rows,
          'verification':{'adaptive_decisions':decisions,'candidate_window_vectors':decisions*3*3,
                           'same_prefix_identity_checks':identities,'baseline_native_checks':verifications}}
 write=lambda p,v:p.write_text(json.dumps(v,indent=2)+'\n')
 write(out/'summary.json',summary);write(ROOT/'verification/recomputed_checks.json',summary['verification'])
 lines=['# Reuse versus fresh selection: final report','',
 'All 20 path constructions completed. All numbers below are recomputed from per-window records. No manuscript or public repository was changed.','',
 '## Frozen predictions','',
 '| Model | P1 numerical band | Network positive | P2 network halved | P2 local change <=0.01 | P2 joint | P3 source not worse | P4 predicted adoption |',
 '|---|---|---|---|---|---|---|---|']
 for m,r in predictions.items():lines.append('| '+m+' | '+' | '.join(str(r[k]) for k in ['P1','P1_network_positive','P2_network','P2_local','P2','P3','P4'])+' |')
 lines+=['','P1 uses final-policy optimism on the full 32-window source audit. Its predeclared band is network 0.02–0.04 and |local|<=0.01. P2 compares summed per-step NLL gain differences against the same fixed eight audit windows in both modes. Results are means of two selection draws with one fixed fit set; these are operational pass/fail rules, not significance tests.','',
 '## Optimism by policy, mode, model and draw','',
 '| Model | Policy | Mode | Draw | Summed step optimism (audit 8) | Final path optimism (audit 8) | Final path optimism (source 32) |',
 '|---|---|---|---:|---:|---:|---:|']
 def fmt(x):return '—' if x is None else f'{x:+.8f}'
 for r in all_rows:
  if r['mode']=='fixed':continue
  lines.append(f"| {r['model']} | {r['policy']} | {r['mode']} | {r['draw']} | {fmt(r['step_optimism'])} | {fmt(r['path_optimism_audit8'])} | {fmt(r['path_optimism_source32'])} |")
 lines+=['','Fresh final-policy selection-window losses are stored individually in each path’s `final_selection_windows.jsonl`; they are not pooled into a selection-set score. Reuse step/path values agree for the SAME audit subset; changing audit 8 to source 32 changes the comparison sample.','',
 '## Final risk, domains kept separate','',
 '| Model | Policy | Mode | Draw | Source NLL | WikiText test NLL | Novel NLL | Total seconds |',
 '|---|---|---|---:|---:|---:|---:|---:|']
 for r in all_rows:lines.append(f"| {r['model']} | {r['policy']} | {r['mode']} | {r['draw'] or '—'} | {r['source_nll']:.8f} | {r['wiki_nll']:.8f} | {r['novel_nll']:.8f} | {r['total_seconds']:.1f} |")
 lines+=['','## Frozen-threshold rule (reuse only)','',
 '| Model | Draw | Selection gain vs local | Adopt network | Source gain vs local | Decision correct on source | Rule source NLL | Rule Wiki NLL | Rule novel NLL |',
 '|---|---:|---:|---|---:|---|---:|---:|---:|']
 for r in p4:lines.append(f"| {r['model']} | {r['draw']} | {r['selection_gain_network_over_local']:+.8f} | {r['adopt_network']} | {r['source_gain_network_over_local']:+.8f} | {r['correct_on_source_audit']} | {r['rule_source_nll']:.8f} | {r['rule_wiki_nll']:.8f} | {r['rule_novel_nll']:.8f} |")
 total=sum(r['total_seconds'] for r in all_rows)
 lines+=['','## Checks and cost','',f'Validated {decisions} adaptive decisions, all candidate/window matrices, 48 real-model same-prefix candidate checks, matched first-step candidates, fixed-audit telescoping and RTN/half native reconstructions on all three audit domains. Total measured path time: {total/3600:.3f} GPU-hours. Timings include audit/logging, fresh final-window evaluation and baseline verification, and exclude one-time worker model loading. Source data, hardware and frozen source hashes are in the plans/manifests.','',
 'Fresh uses 1,024 unique selection windows for Llama and 1,152 for Qwen, versus eight for reuse. It also recomputes teacher/student prefixes. This intervention changes reuse together with unique text coverage; it does not establish a mechanism at equal data budget. The same two source draws and fixed audit windows are correlated observations, not independent population replicates.','',
 '## What this means for Section 9','']
 if not all(v['P1_network_positive'] for v in predictions.values()):
  conclusion='The historical positive reuse optimism did not reproduce in both models. This experiment therefore does not support a general claim that reuse caused the earlier ranking reversal. Report the non-reproduction and the fresh/reuse contrasts as observed; the causal explanation remains unconfirmed. Do not replace this failure with tuned seeds or thresholds.'
 elif not all(v['P2'] for v in predictions.values()):
  conclusion='The frozen P2 criterion failed. Withdraw the proposed operational explanation that avoiding repeated selection-window reuse substantially removes network optimism while leaving local unchanged in these settings. Candidate quality, objective mismatch and domain shift remain alternative questions, not established replacements. These observations do not prove that reuse can never cause optimism.'
 elif not all(v['P3'] for v in predictions.values()):
  conclusion='Fresh data reduced the measured optimism under P2, but did not improve source risk in both models under P3. This supports a restricted statistical effect without establishing that it explains the harmful final decisions or yields an engineering improvement.'
 else:
  conclusion='The frozen P2 and P3 predictions passed in both models: the fresh-window intervention reduced measured network optimism and did not worsen source risk. This supports the reuse hypothesis within these two fixed-fit model conditions, subject to the larger unique-data budget and only two selection draws. It does not establish a universal mechanism or guarantee novel-domain gains.'
 lines.append(conclusion);(out/'FINAL_REPORT.md').write_text('\n'.join(lines)+'\n')
 print(json.dumps({'event':'analysis_complete','predictions':predictions,'gpu_hours':total/3600}),flush=True)
if __name__=='__main__':main()
