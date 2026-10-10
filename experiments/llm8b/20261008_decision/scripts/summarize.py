"""Summarize all frozen outcomes; no best-seed selection or iid-CI claim."""
from pathlib import Path
import json
import statistics
import hashlib
import argparse

root=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser()
parser.add_argument('--results',type=Path,default=root/'results')
results_path=parser.parse_args().results
all_rows=[]
for run in sorted(results_path.iterdir()):
    if not (run/'results.json').exists():continue
    r=json.loads((run/'results.json').read_text())
    meta=json.loads((run/'manifest.json').read_text())
    source_name='replicate.py' if '_replicate_' in run.name else ('task_experiment.py' if '_task_' in run.name else 'experiment.py')
    assert hashlib.sha256((run/source_name).read_bytes()).hexdigest()==meta['source_sha256'],run
    for domain,rr in [('wikitext',r),('gutenberg',r.get('extra_domain',{}))]:
        if not rr:continue
        for policy,v in rr['policies'].items():
            all_rows.append({'run':run.name,'model':Path(meta['model']).name,'seed':meta['config']['seed'],
                'domain':domain,'policy':policy,'nll':v['nll'],'ppl':v['ppl'],
                'fp_nll':rr['teacher']['nll'],'fp_ppl':rr['teacher']['ppl'],
                'construction_seconds':r['policy_construction_seconds'][policy]})
    if 'task_select' in r['policies']:
        previous=None;steps=0;worst=0.
        for line in (run/'decisions.jsonl').read_text().splitlines():
            row=json.loads(line)
            if row['policy']!='task_select':continue
            for choice in row['choices']:
                scores=choice['scores'];base=scores[0]['score'];best=min(x['score'] for x in scores)
                assert best<=base+1e-7
                if previous is not None:worst=max(worst,abs(base-previous))
                previous=best;steps+=1
        assert worst<1e-5,(run.name,worst)
        print(run.name,'selection monotonicity checked:',steps,'steps; continuity error',worst)
(results_path/'all_metrics.json').write_text(json.dumps(all_rows,indent=2)+'\n')
rows=[r for r in all_rows if '_replicate_' in r['run']]
if rows:
    models=sorted({r['model'] for r in rows});domains=sorted({r['domain'] for r in rows})
    for model in models:
        for domain in domains:
            base=[r for r in rows if (r['model'],r['domain'],r['policy'])==(model,domain,'rtn')]
            for field in ['nll','fp_nll']:
                values=[r[field] for r in base]
                assert max(values)-min(values)<1e-7,(model,domain,field,values)
    policies=list(dict.fromkeys(r['policy'] for r in rows))
    lines=['# Fixed replication results','', 'Mean PPL across three calibration draws; the range is seed variability, not a confidence interval.','', '| Model | Domain | Policy | Mean PPL | PPL range | NLL difference vs local | Wins vs local |','|---|---|---|---:|---|---:|---:|']
    for model in models:
        for domain in domains:
            for policy in policies:
                ss=[r for r in rows if (r['model'],r['domain'],r['policy'])==(model,domain,policy)]
                ds=[]
                for r in ss:
                    ref=next(s for s in rows if (s['run'],s['domain'],s['policy'])==(r['run'],domain,'local_select'))
                    ds.append(r['nll']-ref['nll'])
                ps=[r['ppl'] for r in ss]
                lines.append(f'| {model} | {domain} | {policy} | {statistics.mean(ps):.5f} | {min(ps):.5f}–{max(ps):.5f} | {statistics.mean(ds):+.6f} | {sum(x<0 for x in ds)}/{len(ds)} |')
    (results_path/'REPLICATION_SUMMARY.md').write_text('\n'.join(lines)+'\n')
    print('\n'.join(lines))
