import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
import torch
from replicate import quantize,fit_map,correction,block_forward
from transformers import Qwen3Config,Qwen3Model

torch.set_num_threads(1)
torch.manual_seed(18)
w=torch.randn(7,128)
q,c,s,z=quantize(w,return_codes=True)
assert int(c.min())>=0 and int(c.max())<=15
assert torch.equal(q,((c.float()-z)*s).reshape_as(w))
assert torch.equal(quantize(torch.zeros_like(w)),torch.zeros_like(w))
fixture=torch.arange(16).float().repeat(8).reshape(1,128)
assert torch.equal(quantize(fixture),fixture)
for n,d in [(5,11),(15,7)]:
    x=torch.randn(n,d);zz=torch.randn(n,d);w=torch.randn(3,d)
    fit=fit_map(x,zz,1.)
    primal=(w@(x-zz).T@zz)@torch.linalg.inv(zz.T@zz+fit[2]*torch.eye(d))
    assert torch.allclose(correction(w,fit),primal,atol=2e-6,rtol=2e-5)
    assert torch.equal(correction(w,fit_map(zz,zz,1.)),torch.zeros_like(w))
c=Qwen3Config(vocab_size=64,hidden_size=32,intermediate_size=128,num_hidden_layers=2,
              num_attention_heads=4,num_key_value_heads=2,head_dim=8)
m=Qwen3Model(c).eval();ids=torch.randint(0,64,(2,8))
with torch.inference_mode():
    expected=m(ids,use_cache=False).last_hidden_state
    h=m.embed_tokens(ids);pos=torch.arange(8).unsqueeze(0);rot=m.rotary_emb(h,pos)
    for layer in m.layers:h=block_forward(layer,h,rot)
    assert torch.equal(m.norm(h),expected)
print('PASS codebook/roundtrip, dual/primal ridge, zero drift, SDPA block parity')
