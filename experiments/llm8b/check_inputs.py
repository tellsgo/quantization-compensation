"""Verify checkpoint identities and reconstruct every archived token fingerprint on CPU."""
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(8 * 1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--model-key', choices=['qwen3', 'llama3'], required=True)
    p.add_argument('--model', type=Path, required=True)
    p.add_argument('--data', type=Path, required=True)
    p.add_argument('--weights', action='store_true', help='Also hash every checkpoint shard (many GB)')
    a = p.parse_args()
    meta = json.loads((ROOT / 'provenance' / f'{a.model_key}_checkpoint.json').read_text())
    for name, rec in meta.items():
        if name.endswith('.safetensors') and not a.weights:
            continue
        if digest(a.model / name) != rec['sha256']:
            raise ValueError('Checkpoint file mismatch: ' + name)
    import numpy as np
    from transformers import AutoTokenizer
    tok = AutoTokenizer.from_pretrained(a.model, local_files_only=True)
    sources = json.loads((ROOT / 'provenance/data_sources.json').read_text())
    tokens = {}
    for key, name in [('train', 'wikitext2_train.txt'), ('eval', 'wikitext2_test.txt'), ('eval_extra', 'gutenberg_1342_body.txt')]:
        path = a.data / name
        if digest(path) != sources['files'][name]['sha256']:
            raise ValueError('Text mismatch: ' + name)
        tokens[key] = tok.encode(path.read_text(), add_special_tokens=False)
    count = 0
    for record in sorted(ROOT.glob(f'*/results/{a.model_key}_*/data.json')):
        data = json.loads(record.read_text())
        ranges = data.get('offsets') or {k: [[i, i + 512] for i in starts] for k, starts in data['starts'].items()}
        for split, intervals in ranges.items():
            source = tokens[split if split.startswith('eval') else 'train']
            array = np.concatenate([np.asarray(source[lo:hi], dtype=np.int64) for lo, hi in intervals]).reshape(-1, 512)
            if hashlib.sha256(array.tobytes()).hexdigest() != data['token_hashes'][split]:
                raise ValueError(f'Token mismatch: {record.parent.name} {split}')
            count += 1
    print(f'PASS: {a.model_key} checkpoint metadata and {count} token-array fingerprints; weights checked={a.weights}')


if __name__ == '__main__':
    main()
