"""Deterministic publication checks; does not run model inference or Monte Carlo."""
from pathlib import Path
import gzip, hashlib, json, math, shutil, subprocess, sys, tempfile
import numpy as np
ROOT = Path(__file__).resolve().parents[1]
N = ROOT / 'numerics'
def read(p): return json.loads(p.read_text())
def close(a,b): assert math.isclose(a,b,rel_tol=2e-10,abs_tol=2e-12),(a,b)
r=read(N/'results_sim1.json'); c=read(N/'crosscheck_numpy.json')
assert len(r['fixed'])==len(r['random'])==84 and len(r['gain_paired'])==28
for row in r['gain_paired']:
    raw=c['B1_per_teacher'][repr(row['nu'])]
    col=[1,2,4,8,16,32,64].index(row['L'])
    b=np.asarray(raw['num']['0.0'])[:,col]; q=np.asarray(raw['num']['1.0'])[:,col]
    assert len(b)==len(q)==100
    gain=10/math.log(10)*math.log(b.mean()/q.mean())
    se=10/math.log(10)*np.std(b/b.mean()-q/q.mean(),ddof=1)/math.sqrt(len(b))
    close(gain,row['gain_db']); close(se,row['se_db'])
with tempfile.TemporaryDirectory() as tmp:
    tmp=Path(tmp)
    for name in ['results_sim1.json','sim2_gain_split.json','results_sim3.json','make_figs.py']: shutil.copy2(N/name,tmp/name)
    subprocess.run([sys.executable,'make_figs.py'],cwd=tmp,check=True)
    for name in ['fig_gain.tex','fig_relu.tex','tab_split.tex']:
        assert (tmp/name).read_bytes()==(N/name).read_bytes(),name
out=ROOT/'reproduced_figures';out.mkdir(exist_ok=True)
for name in ['fig_gain.tex','fig_relu.tex','tab_split.tex']:shutil.copy2(N/name,out/name)
expected={'smol135_wikitext':(210,207,19),'smol135_gutenberg':(210,207,0),'pythia160_wikitext':(48,46,11),'pythia160_gutenberg':(48,46,12)}
for cell,(total,eligible,harm) in expected.items():
    rows=[json.loads(l) for l in gzip.decompress((ROOT/'diagnostics/data'/f'{cell}.jsonl.gz').read_bytes()).decode().splitlines()]
    assert len(rows)==total*34 and all(x['quality_pass'] for x in rows)
    det=[x for x in rows if x['alpha']==.5 and x['mode']=='deterministic']
    assert len(det)==total
    assert sum(x['cal']['eligible_ratio'] for x in det)==eligible
    assert sum(x['holdout']['actual_harm_tolerant'] for x in det)==harm
    assert not any(x['cal']['actual_harm_tolerant'] or x['cal']['fixed_harm_tolerant'] for x in det)
range_rows=[json.loads(l) for l in gzip.decompress((ROOT/'diagnostics/data/range_energy.jsonl.gz').read_bytes()).decode().splitlines()]
for cell,percent in zip(expected,[.19,.21,9.1,9.3]):
    rows=[x for x in range_rows if x['cell']==cell and x['alpha']==.5 and x['bits']==4]
    measured=100*sum(x['overload_count'] for x in rows)/sum(x['weights'] for x in rows)
    assert abs(measured-percent)<(.005 if percent<1 else .05),(cell,measured)
subprocess.run([sys.executable,str(N/'saved_witnesses/replay_fixed_witnesses.py'),'--replay'],check=True)
lean=ROOT/'lean'
for line in (lean/'SHA256SUMS').read_text().splitlines():
    digest,path=line.split(maxsplit=1); path=path.lstrip('*')
    assert hashlib.sha256((lean/path).read_bytes()).hexdigest()==digest,path
print('PASS: byte-identical figures; 28 paired uncertainties; diagnostic counts and ranges; 3 exact witness replays; Lean artifact hashes. No new Lean build.')
