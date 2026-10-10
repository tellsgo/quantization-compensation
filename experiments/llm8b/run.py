"""Portable launcher for the frozen experiment programs. Does not alter their math."""
from pathlib import Path
import argparse
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
CAMPAIGNS = {
    'decision': ('20261008_decision', 'replicate.py'),
    'selection': ('20261008_selection_controls', 'scale_selection.py'),
    'suffix': ('20261008_suffix_interaction', 'probe.py'),
    'adaptive': ('20261009_adaptive_strength', 'pilot.py'),
}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('campaign', choices=CAMPAIGNS)
    p.add_argument('--model', type=Path, help='Local checkpoint directory')
    p.add_argument('--data', type=Path, help='Prepared text directory')
    p.add_argument('--draw', type=int, choices=[1, 2, 3], default=1)
    p.add_argument('--selection-tokens', type=int, choices=[4096, 16384, 32768], default=4096)
    p.add_argument('--base', type=Path, help='Fresh parent run; decision for selection, 4K selection for suffix/adaptive')
    p.add_argument('--output', type=Path, required=True, help='New, nonexistent run directory')
    p.add_argument('--dry-run', action='store_true', help='Check paths and show invocation without importing CUDA libraries')
    a = p.parse_args()
    folder, program = CAMPAIGNS[a.campaign]
    if a.output.exists():
        p.error('output must not already exist')
    if a.campaign != 'decision' and a.draw == 3:
        p.error('only decision has a third draw')
    if a.campaign in ['decision', 'selection']:
        if a.model is None or not a.model.is_dir() or a.data is None:
            p.error('--model must be an existing checkpoint directory; --data is required')
        for name in ['wikitext2_train.txt', 'wikitext2_test.txt', 'gutenberg_1342_body.txt']:
            if not (a.data / name).is_file():
                p.error('missing data file: ' + name)
    if a.campaign != 'decision':
        if a.base is None or not (a.base / 'manifest.json').is_file():
            p.error('--base must contain a completed parent run')
        if json.loads((a.base / 'progress.json').read_text())['status'] != 'complete':
            p.error('parent run is incomplete')
    config = {
        'decision': f'replicate_{a.draw}.json',
        'selection': f'draw{a.draw}_n{a.selection_tokens}.json',
        'suffix': 'fixed.json',
        'adaptive': 'pilot.json',
    }[a.campaign]
    cfg = json.loads((ROOT / folder / 'configs' / config).read_text())
    cmd = [sys.executable, str(ROOT / folder / 'src' / program), '--output', str(a.output.resolve())]
    if a.campaign in ['decision', 'selection']:
        cmd += ['--model', str(a.model.resolve()), '--train', str((a.data / 'wikitext2_train.txt').resolve()),
                '--evaluation', str((a.data / 'wikitext2_test.txt').resolve())]
        extra = str((a.data / 'gutenberg_1342_body.txt').resolve())
        if a.campaign == 'decision':
            cfg['evaluation_extra'] = extra
        else:
            cmd += ['--extra', extra, '--base-run', str(a.base.resolve())]
    else:
        cmd += ['--base', str(a.base.resolve())]
    # The runner saves the resolved config in its own manifest before the temp file disappears.
    with tempfile.TemporaryDirectory(prefix='quantization-config-') as temp:
        path = Path(temp) / config
        path.write_text(json.dumps(cfg, indent=2) + '\n')
        cmd += ['--config', str(path)]
        if a.dry_run:
            print(json.dumps({'command': cmd, 'resolved_config': cfg}, indent=2))
        else:
            subprocess.run(cmd, check=True)


if __name__ == '__main__':
    main()
