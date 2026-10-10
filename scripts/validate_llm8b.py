"""Recalculate manuscript experiment numbers from distributed per-run records.

No inference, new experiment, or import of the production analysis scripts.
"""
from pathlib import Path
import csv
import hashlib
import json
import math
import re
import statistics as st
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
EXPERIMENTS = ROOT / 'experiments/llm8b'
OUT = ROOT / 'reproduced_llm8b'
OUT.mkdir(exist_ok=True)
SOURCES = {}


def read(path):
    raw = path.read_bytes()
    SOURCES[str(path.relative_to(ROOT))] = hashlib.sha256(raw).hexdigest()
    return raw.decode()


def obj(path):
    return json.loads(read(path))


def lines(path):
    return [json.loads(x) for x in read(path).splitlines() if x.strip()]


def check_run(path):
    assert obj(path / 'progress.json')['status'] == 'complete'
    meta = obj(path / 'manifest.json')
    hashes = meta['source_sha256']
    if isinstance(hashes, str):
        hashes = {'replicate.py': hashes}
    for name, digest in hashes.items():
        read(path / name)
        assert SOURCES[str((path / name).relative_to(ROOT))] == digest
    return meta


def nll(record):
    value = st.mean(record['sequence_nll'])
    assert abs(value - record['nll']) < 1e-12
    assert abs(math.exp(value) - record['ppl']) < 1e-10
    return value


# Validate the complete public inventory, including source and numeric archives.
inventory = obj(EXPERIMENTS / 'provenance/FILES.json')
for record in inventory['files']:
    path = ROOT / record['path']
    assert hashlib.sha256(path.read_bytes()).hexdigest() == record['release_sha256'], record['path']
    if path.suffix == '.py' or path.name in ['results.json','decisions.jsonl','interventions.jsonl','slices.jsonl']:
        assert record['original_sha256'] == record['release_sha256'], record['path']



policies = ['rtn', 'qep_half', 'local_select', 'lookahead_select', 'task_select', 'directional_select']
paper_rows = [
    [12.643,12.320,12.119,12.199,11.970,11.870],
    [12.875,12.618,12.665,12.552,12.613,12.582],
    [8.264,8.031,8.018,8.017,8.075,8.028],
    [5.786,5.625,5.586,5.627,5.766,5.689],
]
paper_wins = [[1,2,3],[3,2,1],[2,0,0],[1,0,1]]
table, decisions, timings, comparisons = [], [], [], []
for model in ['qwen3','llama3']:
    results = []
    for draw in [1,2,3]:
        p = EXPERIMENTS / f'20261008_decision/results/{model}_replicate_{draw}'
        check_run(p)
        r = obj(p / 'results.json')
        nll(r['teacher']); nll(r['extra_domain']['teacher'])
        results.append(r)
        ratios = r['policy_construction_seconds']
        timings.append({'model':model,'draw':draw,'gradient_over_local':ratios['directional_select']/ratios['local_select']})
        previous = None
        for row in lines(p / 'decisions.jsonl'):
            if row['policy'] != 'task_select':
                continue
            for c in row['choices']:
                s = {v['alpha']:v['score'] for v in c['scores']}
                chosen = s[c['alpha']]
                assert chosen <= s[0.] + 1e-8
                assert chosen == min(s.values())
                continuity = None if previous is None else abs(s[0.] - previous)
                decisions.append({'model':model,'draw':draw,'layer':row['layer'],'group':c['group'],
                                  'chosen_minus_zero':chosen-s[0.], 'continuity_error':continuity})
                previous = chosen
    for domain in ['wiki','novel']:
        rr = [r['policies'] if domain=='wiki' else r['extra_domain']['policies'] for r in results]
        # Validate every saved policy, including the one omitted from Table 4.
        for r in rr:
            for v in r.values(): nll(v)
        for i, p in enumerate(policies):
            vals = [math.exp(nll(r[p])) for r in rr]
            row = {'model':model,'text':domain,'policy':p,'mean_ppl':st.mean(vals),
                   'wins_vs_local':sum(nll(r[p]) < nll(r['local_select']) for r in rr)}
            idx = (0 if model=='qwen3' else 2) + (domain=='novel')
            assert round(row['mean_ppl'],3) == paper_rows[idx][i], row
            if i>=3: assert row['wins_vs_local'] == paper_wins[idx][i-3]
            table.append(row)
        for draw,r in enumerate(rr,1):
            comparisons.append({'model':model,'text':domain,'draw':draw,
                'half_beats_rtn':nll(r['qep_half']) < nll(r['rtn']),
                'network_beats_rtn':nll(r['task_select']) < nll(r['rtn']),
                'network_beats_local':nll(r['task_select']) < nll(r['local_select'])})
assert len(decisions)==816

selection=[]
for model in ['qwen3','llama3']:
    for count in [4096,16384,32768]:
        run_diffs=[]
        for draw in [1,2]:
            p=EXPERIMENTS/f'20261008_selection_controls/results/{model}_draw{draw}_n{count}'
            check_run(p);full=obj(p/'results.json')
            for metric in full['teacher'].values(): nll(metric)
            r=full['policies']
            for policy in r:
                for metric in r[policy].values():nll(metric)
            ds={k:nll(r['task_select'][k])-nll(r['local_select'][k]) for k in ['select','diag','eval','eval_extra']}
            run_diffs.append({'draw':draw,**ds})
        selection.append({'model':model,'selection_tokens':count,'draws':run_diffs,
                          'means':{k:st.mean(x[k] for x in run_diffs) for k in ['select','diag','eval','eval_extra']}})

suffix=[]
for model in ['qwen3','llama3']:
    for draw in [1,2]:
        p=EXPERIMENTS/f'20261008_suffix_interaction/results/{model}_draw{draw}'
        check_run(p)
        for r in lines(p/'interventions.jsonl'):
            c=r['candidates'];a=min(c,key=lambda x:x['select']['rtn']);b=min(c,key=lambda x:x['select']['completed'])
            old=b['select']['rtn']-a['select']['rtn'];new=a['select']['completed']-b['select']['completed']
            diag_old=b['diag']['rtn']-a['diag']['rtn'];diag_new=a['diag']['completed']-b['diag']['completed']
            robust=old>1e-4 and new>1e-4
            suffix.append({'model':model,'draw':draw,'layer':r['layer'],'group':r['group'],
                'terminal':r['terminal_control'],'raw_switch':a['alpha']!=b['alpha'],'robust':robust,
                'diag_replicates':robust and diag_old>1e-4 and diag_new>1e-4})


def ranks(values):
    # Average rank for ties, derived without production helper imports.
    return [sum(y<x for y in values)+(sum(y==x for y in values)+1)/2 for x in values]


def correlation(x,y):
    x,y=ranks(x),ranks(y);mx,my=st.mean(x),st.mean(y)
    return sum((a-mx)*(b-my) for a,b in zip(x,y))/math.sqrt(sum((a-mx)**2 for a in x)*sum((b-my)**2 for b in y))


adaptive=[];raw_centers=[]
for model in ['qwen3','llama3']:
    for draw in [1,2]:
        p=EXPERIMENTS/f'20261009_adaptive_strength/results/{model}_draw{draw}'
        meta=check_run(p);rows=lines(p/'slices.jsonl');assert len(rows)==12
        values={m:[] for m in ['zero','half','center','fixed2','grid10']};cors=[];fixed_zero=0;center_worse=0
        for r in rows:
            raw_centers.append(r['estimate']['dot']/r['estimate']['direction_energy'])
            grid=[x for x in r['curve'] if x['alpha'] in [0.]+meta['config']['grid']];assert len(grid)==11
            predictions=[r['outcomes']['zero']['select_loss']-2*x['alpha']*r['estimate']['dot']+x['alpha']**2*r['estimate']['direction_energy'] for x in grid]
            assert max(abs(a-x['frozen_prediction']) for a,x in zip(predictions,grid))<1e-10
            cors.append(correlation(predictions,[x['select_loss'] for x in grid]))
            for m in values: values[m].append(r['outcomes'][m]['diag_loss']/r['target_energy']['diag'])
            candidates=[x for x in r['curve'] if x['alpha'] in [0.,.5,1.]]
            selected=min(candidates,key=lambda x:(x['select_loss'],x['alpha']))
            assert selected['alpha']==r['outcomes']['fixed2']['alpha']
            fixed_zero += selected['alpha']==0
            center_worse += r['outcomes']['center']['diag_loss']>r['outcomes']['half']['diag_loss']+1e-8*max(r['target_energy']['diag'],abs(r['outcomes']['half']['diag_loss']))
        v={k:st.mean(x) for k,x in values.items()}
        adaptive.append({'model':model,'draw':draw,'spearman_mean':st.mean(cors),
            'center_improvement_vs_half_pct':100*(1-v['center']/v['half']),
            'fixed_retained_grid_gain_pct':100*(v['zero']-v['fixed2'])/(v['zero']-v['grid10']),
            'fixed_zero_choices':fixed_zero,'center_worse_than_half_slices':center_worse})

result={'table4':table,'replicate_comparisons':comparisons,'network_decisions':{'count':len(decisions),
    'max_chosen_minus_zero':max(r['chosen_minus_zero'] for r in decisions),
    'max_continuity_error':max(r['continuity_error'] or 0 for r in decisions)},
    'timings':timings,'selection_controls':selection,
    'suffix':{'nonterminal':sum(not x['terminal'] for x in suffix),'robust':sum(x['robust'] for x in suffix),
              'diagnostic_replicated':sum(x['diag_replicates'] for x in suffix)},
    'adaptive':adaptive,'unclipped_centers':{'above_one':sum(x>1 for x in raw_centers),'maximum':max(raw_centers)},
    'source_sha256':SOURCES}
(OUT/'recomputed.json').write_text(json.dumps(result,indent=2)+'\n')
with (OUT/'table4.csv').open('w') as f:
    w=csv.DictWriter(f,fieldnames=list(table[0]));w.writeheader();w.writerows(table)
print('PASS: 816 greedy decisions; 12 selection-size runs; 48 nonterminal suffix states; 48 adaptive slices.')
print('PASS: 24 Table 4 cells, 12 win counts; all stored NLL/PPL pairs recomputed from sequence NLLs.')

# Check selection continuity and non-overlap/nesting from the saved ranges.
monotone = {'task_select': 0, 'block_select': 0}
for model in ['qwen3','llama3']:
    for draw in [1,2]:
        samples = []
        for size in [4096,16384,32768]:
            run = EXPERIMENTS / f'20261008_selection_controls/results/{model}_draw{draw}_n{size}'
            data = obj(run / 'data.json')
            starts = data['starts']
            for split, number in [('cal',4),('select',size//512),('diag',16)]:
                assert len(starts[split]) == len(set(starts[split])) == number
                assert all(i % 512 == 0 for i in starts[split])
            for a,b in [('cal','select'),('cal','diag'),('select','diag')]:
                assert not set(starts[a]) & set(starts[b])
            if samples:
                assert starts['select'][:len(samples[-1]['select'])] == samples[-1]['select']
                assert all(starts[k] == samples[0][k] for k in ['cal','diag','eval','eval_extra'])
            samples.append(starts)
            previous = None
            for row in lines(run / 'decisions.jsonl'):
                policy = row['policy']
                if policy not in monotone: continue
                block_previous = None
                for choice in row['choices']:
                    scores = {v['alpha']:v['score'] for v in choice['scores']}
                    chosen = scores[choice['alpha']]
                    assert chosen == min(scores.values()) and chosen <= scores[0.] + 1e-8
                    old = previous if policy == 'task_select' else block_previous
                    if old is not None: assert abs(old - scores[0.]) < 1e-5
                    if policy == 'task_select': previous = chosen
                    else: block_previous = chosen
                    monotone[policy] += 1
            final = obj(run / 'results.json')['policies']['task_select']['select']['nll']
            assert abs(previous - final) < 1e-5
assert monotone == {'task_select':1632,'block_select':1632}, monotone

# Historical native-forward receipts; this invocation performs no inference.
receipt_count = 0
for p in (EXPERIMENTS / '20261008_decision/results').glob('*/native_verification.json'):
    for v in obj(p).values():
        assert v['absolute_difference'] < 1e-6
        receipt_count += 1
assert receipt_count == 8
receipts = list((EXPERIMENTS / '20261008_selection_controls/results/verification').glob('*.json'))
assert len(receipts) == 6
for p in receipts:
    r = obj(p)
    for v in r['checks'].values(): assert v['max_sequence_difference'] < 1e-6
for p in (EXPERIMENTS / '20261009_adaptive_strength/results').glob('*/native_parity.json'):
    for v in obj(p).values(): assert v['difference'] < 1e-6
assert result['suffix'] == {'nonterminal':48,'robust':11,'diagnostic_replicated':0}
assert result['unclipped_centers']['above_one'] == 7
assert sum(r['center_worse_than_half_slices'] for r in adaptive) == 1
assert sum(r['half_beats_rtn'] for r in comparisons) == 12

# Rebuild full reports in scratch space; do not write into the frozen archive.
for campaign, script in [('20261008_decision','summarize.py'),
                         ('20261008_suffix_interaction','analyze.py'),
                         ('20261009_adaptive_strength','analyze.py')]:
    base = EXPERIMENTS / campaign
    with tempfile.TemporaryDirectory() as temp:
        scratch = Path(temp) / 'results'
        shutil.copytree(base / 'results', scratch)
        original_names = {p.name for p in scratch.iterdir()}
        subprocess.run([sys.executable, str(base / 'scripts' / script), '--results', str(scratch)], check=True, stdout=subprocess.PIPE)
        target = OUT / campaign
        target.mkdir(exist_ok=True)
        for p in scratch.iterdir():
            if p.name not in original_names and p.is_file(): shutil.copy2(p, target / p.name)
for test in sorted(EXPERIMENTS.glob('*/tests/test_*.py')):
    if test.parent.parent.name == '20261008_decision': continue
    subprocess.run([sys.executable, str(test)], check=True)
print('PASS: archive hashes, nested ranges, 3264 selection decisions, native receipts, full reports and analysis tests.')
print('Outputs: reproduced_llm8b/ (no GPU inference or new model-performance claim).')
