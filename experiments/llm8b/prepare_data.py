"""Acquire the public texts and require the archived transformed-text hashes."""
from pathlib import Path
import argparse
import hashlib
import io
import json
import re
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parent


def fetch(url):
    with urlopen(Request(url, headers={'User-Agent': 'quantization-compensation-reproduction'}), timeout=90) as r:
        return r.read()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    meta = json.loads((ROOT / 'provenance/data_sources.json').read_text())
    a.output.mkdir(parents=True, exist_ok=True)
    for split in ['train', 'test']:
        name = f'wikitext2_{split}.txt'
        path = a.output / name
        if path.exists():
            text = path.read_bytes()
        else:
            import pyarrow.parquet as pq
            url = meta['wikitext_test_source'].replace('/test-00000-', '/' + split + '-00000-')
            raw = fetch(url)
            if split == 'test' and hashlib.sha256(raw).hexdigest() != meta['wikitext_test_parquet_sha256']:
                raise ValueError('Pinned WikiText test parquet hash mismatch')
            rows = pq.read_table(io.BytesIO(raw))['text'].to_pylist()
            text = '\n\n'.join(t for t in rows if t.strip()).encode('utf-8')
        if hashlib.sha256(text).hexdigest() != meta['files'][name]['sha256']:
            raise ValueError(f'{name}: transformed-text hash mismatch; no replacement saved')
        if not path.exists():
            path.write_bytes(text)
        print('PASS', name)
    name = 'gutenberg_1342_body.txt'
    path = a.output / name
    if path.exists():
        text = path.read_bytes()
    else:
        raw = fetch(meta['gutenberg_source'])
        # Normalize CRLF exactly as the original Python text-file reader did.
        content = raw.decode('utf-8-sig').replace('\r\n', '\n').replace('\r', '\n')
        start = re.search(r'^\*\*\* START OF THE PROJECT GUTENBERG EBOOK[^\n]*\*\*\*\s*$', content, re.M)
        end = re.search(r'^\*\*\* END OF THE PROJECT GUTENBERG EBOOK[^\n]*\*\*\*\s*$', content, re.M)
        if not start or not end:
            raise ValueError('Gutenberg wrapper markers missing')
        text = content[start.end():end.start()].strip().encode('utf-8')
    if hashlib.sha256(text).hexdigest() != meta['files'][name]['sha256']:
        raise ValueError('Gutenberg body differs from the archived version; use an original copy with the recorded hash')
    if not path.exists():
        path.write_bytes(text)
    print('PASS', name)


if __name__ == '__main__':
    main()
