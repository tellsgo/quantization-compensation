"""Replay the frozen 20-path reuse/fresh campaign in a new directory."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys

ARCHIVE = Path(__file__).resolve().parent / '20261012_reuse_fresh'


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(8 * 1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def read(path):
    return json.loads(path.read_text())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--models', type=Path, required=True,
                        help='Directory containing Qwen3-8B and Meta-Llama-3-8B')
    parser.add_argument('--data', type=Path, required=True, help='Prepared public texts')
    parser.add_argument('--output', type=Path, required=True, help='New, nonexistent directory')
    parser.add_argument('--prepare-only', action='store_true', help='Verify and tokenize inputs, without model inference')
    parser.add_argument('--dry-run', action='store_true', help='Show invocation without creating files or importing model libraries')
    args = parser.parse_args()
    if args.output.exists():
        parser.error('--output must not exist; archived results are never overwritten')
    if args.output.resolve().is_relative_to(ARCHIVE.resolve()):
        parser.error('--output must be outside the frozen archive')
    for model in ['Qwen3-8B', 'Meta-Llama-3-8B']:
        if not (args.models / model).is_dir():
            parser.error('missing checkpoint directory: ' + model)
    for filename in ['wikitext2_train.txt', 'wikitext2_test.txt', 'gutenberg_1342_body.txt']:
        if not (args.data / filename).is_file():
            parser.error('missing prepared text: ' + filename)

    freeze = read(ARCHIVE / 'docs/specs/FROZEN.json')
    for name, expected in freeze['files'].items():
        if digest(ARCHIVE / name) != expected:
            raise ValueError('Public frozen file changed: ' + name)
    output = args.output.resolve()
    prepare = [sys.executable, str(output / 'scripts/prepare.py'),
               '--models', str(args.models.resolve()), '--data', str(args.data.resolve())]
    workers = [[sys.executable, str(output / 'src/run.py'), '--model-key', key]
               for key in ['qwen3', 'llama3']]
    if args.dry_run:
        print(json.dumps({'prepare': prepare, 'workers_sequential': workers,
                          'paths': 20, 'new_directory': str(output)}, indent=2))
        return

    # Check every original checkpoint shard before any inference. Never fetch weights.
    inventory = read(ARCHIVE / 'verification/checkpoint_identity.json')['sha256']
    for key, folder in [('qwen3', 'Qwen3-8B'), ('llama3', 'Meta-Llama-3-8B')]:
        for filename, expected in inventory[key].items():
            if digest(args.models / folder / filename) != expected:
                raise ValueError('Checkpoint fingerprint mismatch: ' + folder + '/' + filename)

    output.mkdir(parents=True)
    for folder in ['src', 'scripts', 'tests', 'configs', 'docs']:
        shutil.copytree(ARCHIVE / folder, output / folder,
                        ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
    (output / 'verification').mkdir()
    (output / 'results').mkdir()
    subprocess.run(prepare, check=True, cwd=output)
    # Relocation is the only permitted difference in a regenerated plan.
    for key in ['qwen3', 'llama3']:
        generated = read(output / 'inputs' / key / 'plan.json')
        expected = read(ARCHIVE / 'inputs' / key / 'plan.json')
        generated.pop('checkpoint'); expected.pop('checkpoint')
        if generated != expected:
            raise ValueError('Regenerated token fingerprints or window plan differ: ' + key)
    replay_freeze = {'status': 'Replay input/source snapshot; original predictions unchanged',
                     'original_freeze_sha256': freeze['original_freeze_sha256'],
                     'public_freeze_sha256': digest(ARCHIVE / 'docs/specs/FROZEN.json'),
                     'files': {name: digest(output / name) for name in freeze['files']}}
    (output / 'docs/specs/FROZEN.json').write_text(json.dumps(replay_freeze, indent=2) + '\n')
    (output / 'verification/input_checks.json').write_text(json.dumps({
        'status': 'PASS', 'checkpoint_files': sum(map(len, inventory.values())),
        'plans_match_archive_except_checkpoint_location': True,
        'freeze_sha256': digest(output / 'docs/specs/FROZEN.json')}, indent=2) + '\n')
    print('PASS: complete checkpoint hashes, public text/token hashes, fitting tokens and both frozen window plans.', flush=True)
    if args.prepare_only:
        print('Inputs ready. Run each src/run.py worker, then scripts/analyze.py, in this output directory.')
        return
    for command in workers:
        subprocess.run(command, check=True, cwd=output)
    subprocess.run([sys.executable, str(output / 'scripts/analyze.py')], check=True, cwd=output)


if __name__ == '__main__':
    main()
