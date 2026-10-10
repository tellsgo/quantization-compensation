"""Independent full native-model forward check for FP and RTN on saved tokens."""
import argparse
import json
from pathlib import Path
import math
import numpy as np
import torch
from transformers import AutoModelForCausalLM

@torch.inference_mode()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--run',required=True);a=ap.parse_args()
    run=Path(a.run);manifest=json.loads((run/'manifest.json').read_text())
    results=json.loads((run/'results.json').read_text());cfg=manifest['config']
    torch.set_num_threads(4);torch.backends.cuda.matmul.allow_tf32=False
    model=AutoModelForCausalLM.from_pretrained(manifest['model'],dtype=torch.bfloat16,
        attn_implementation='sdpa',local_files_only=True).cuda().eval()
    evidence={}
    for mode in ['fp','rtn']:
        if mode=='rtn':
            # Independent implementation of the specified group codebook.
            for layer in model.model.layers:
                for name,mod in layer.named_modules():
                    if not isinstance(mod,torch.nn.Linear):continue
                    w=mod.weight.float();view=w.reshape(w.shape[0],-1,cfg['group_size'])
                    low=view.min(dim=-1,keepdim=True).values.clamp(max=0)
                    high=view.max(dim=-1,keepdim=True).values.clamp(min=0)
                    levels=(1<<cfg['bits'])-1
                    step=((high-low)/levels).clamp(min=torch.finfo(torch.float32).tiny)
                    origin=(-low/step).round().clamp(0,levels)
                    integer=(view/step+origin).round().clamp(0,levels)
                    mod.weight.copy_(((integer-origin)*step).reshape_as(w))
        for split,key in [('eval','wikitext'),('eval_extra','gutenberg')]:
            tokens=torch.from_numpy(np.load(run/f'{split}_tokens.npy')).cuda()
            # Native parent model constructs its own positions, rotary terms and mask.
            hidden=model.model(input_ids=tokens,use_cache=False).last_hidden_state
            losses=[]
            for i in range(len(tokens)):
                logits=model.lm_head(hidden[i:i+1])
                losses.append(float(torch.nn.functional.cross_entropy(
                    logits[:,:-1,:].float().reshape(-1,logits.shape[-1]),tokens[i:i+1,1:].reshape(-1))))
            value=sum(losses)/len(losses)
            ref=results if split=='eval' else results['extra_domain']
            expected=ref['teacher']['nll'] if mode=='fp' else ref['policies']['rtn']['nll']
            difference=abs(value-expected)
            assert difference<1e-6,(mode,key,value,expected,difference)
            evidence[f'{mode}_{key}']={'nll':value,'ppl':math.exp(value),'recorded_nll':expected,'absolute_difference':difference}
    (run/'native_verification.json').write_text(json.dumps(evidence,indent=2)+'\n')
    print(json.dumps(evidence))

if __name__=='__main__':main()
