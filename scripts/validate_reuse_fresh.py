"""Verify the public archive and recompute reuse/fresh results without model inference."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'experiments/llm8b/20261012_reuse_fresh'
OUT = ROOT / 'reproduced_llm8b/reuse_fresh'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
obj = lambda p: json.loads(p.read_text())

original = obj(BASE / 'provenance/ORIGINAL_FREEZE.json')
public = obj(BASE / 'docs/specs/FROZEN.json')
original_digest = sha(BASE / 'provenance/ORIGINAL_FREEZE.json')
assert public['original_freeze_sha256'] == original_digest
for name, expected in public['files'].items():
    assert sha(BASE / name) == expected, name
for record in obj(BASE / 'provenance/FILES.json')['files']:
    assert sha(BASE / record['path']) == record['release_sha256'], record['path']
    if record['change'] == 'none':
        assert record['original_sha256'] == record['release_sha256']
    source = record['original_path']
    if source in original['files']:
        assert record['original_sha256'] == original['files'][source]
    if Path(record['path']).name in ['decisions.jsonl', 'results.json', 'final_selection_windows.jsonl']:
        assert record['change'] == 'none'
    if record['path'].startswith('src/') or record['path'] == 'scripts/analyze.py':
        assert record['change'] == 'none'

for model in ['qwen3', 'llama3']:
    plan_name = 'inputs/' + model + '/plan.json'
    plan = obj(BASE / plan_name)
    meta = obj(BASE / 'results' / model / 'manifest.json')
    assert meta['frozen_sha256'] == original_digest
    assert meta['plan_sha256'] == sha(BASE / plan_name)
    assert meta['original_plan_sha256'] == original['files'][plan_name]
    for name, expected in meta['source_sha256'].items():
        assert sha(BASE / 'src' / name) == expected
    excluded = set(plan['fit_starts'] + plan['source_audit_starts'] + plan['historical_diag_excluded'])
    assert len(set(plan['source_audit_starts'])) == 32
    assert plan['step_audit_starts'] == plan['source_audit_starts'][:8]
    for draw in plan['draws'].values():
        starts = sum(draw['fresh'], [])
        assert len(set(starts)) == len(starts) == plan['steps'] * 8
        assert not set(starts) & excluded
        assert draw['reuse'] == draw['fresh'][0]
        assert all(s % 512 == 0 and s + 512 <= plan['texts']['train']['tokens'] for s in starts)
    for path in (BASE / 'results' / model).glob('*/results.json'):
        final = obj(path)['final']
        assert final['source']['starts'] == plan['source_audit_starts']
        for key, split in [('wiki', 'eval'), ('novel', 'eval_extra')]:
            assert final[key]['starts'] == list(range(*plan['audit_ranges'][split], 512))

# The frozen analyzer validates all candidate/window vectors, selector actions,
# telescoping, native receipts, fresh unpooled records and both P1/P2 definitions.
# Run in scratch space so validation cannot rewrite the published observations.
with tempfile.TemporaryDirectory(prefix='reuse-fresh-check-') as directory:
    scratch = Path(directory) / 'campaign'
    shutil.copytree(BASE, scratch, ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
    subprocess.run([sys.executable, str(scratch / 'scripts/analyze.py')],
                   check=True, stdout=subprocess.PIPE, text=True)
    OUT.mkdir(parents=True, exist_ok=True)
    for name in ['results/summary.json', 'results/all_metrics.csv', 'results/FINAL_REPORT.md',
                 'verification/recomputed_checks.json']:
        assert (scratch / name).read_bytes() == (BASE / name).read_bytes(), name
        shutil.copy2(scratch / name, OUT / Path(name).name)
subprocess.run([sys.executable, str(BASE / 'tests/test_design.py')], check=True)
summary = obj(OUT / 'summary.json')
assert len(summary['paths']) == 20
assert summary['verification']['adaptive_decisions'] == 2176
assert summary['verification']['same_prefix_identity_checks'] == 48
assert len(summary['verification']['baseline_native_checks']) == 12
assert all(p['P1_network_positive'] and not p['P1'] and not p['P2'] and not p['P3']
           for p in summary['predictions'].values())
assert summary['predictions']['qwen3']['P4'] and not summary['predictions']['llama3']['P4']
assert len(summary['threshold_rule']) == 4 and all(r['correct_on_source_audit'] for r in summary['threshold_rule'])
print('PASS: original/public provenance; unchanged numeric records and numerical runners; disjoint frozen windows.')
print('PASS: 20 paths, 2176 decisions, 48 candidate-identity checks, 12 native-baseline receipts; P1–P4 recomputed.')
print('Outputs: reproduced_llm8b/reuse_fresh/ (historical observations; no GPU inference).')
