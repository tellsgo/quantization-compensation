"""Measure the original finite-codebook grid on captured weights and corrections."""
from pathlib import Path
import json
import numpy as np
from finite_core import evaluate, derive_seed
ROOT=Path(__file__).resolve().parent
manifest=json.loads((ROOT/'prepared_manifest.json').read_text())
with (ROOT/'range_energy_rerun.jsonl').open('x') as out:
    for model,meta in manifest['models'].items():
        for dataset in ['wikitext','gutenberg']:
            for module in meta['modules']:
                folder=ROOT/'runs'/f'{model}_{dataset}'/module['name']
                w=np.load(folder/'weight.npy',allow_pickle=False).astype(np.float64)
                c=np.load(folder/'correction.npy',allow_pickle=False)
                for alpha in [0.,.5,1.]:
                    for bits in [2,3,4]:
                        r=evaluate(w,c,alpha,bits,derive_seed(meta['repo'],module['name']))
                        r.update(model=model,dataset=dataset,cell=f'{model}_{dataset}',module=module['name'],alpha=alpha,bits=bits)
                        out.write(json.dumps(r,allow_nan=False)+'\n');out.flush()
