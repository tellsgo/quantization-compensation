"""Native suffix gradient and causal-mask checks, without a model checkpoint."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
import torch
from transformers import Qwen3Config,Qwen3ForCausalLM
from torch.nn.functional import cross_entropy
from replicate import block_forward

torch.set_num_threads(1)
torch.manual_seed(31)
config=Qwen3Config(vocab_size=64,hidden_size=32,intermediate_size=128,
    num_hidden_layers=2,num_attention_heads=4,num_key_value_heads=2,head_dim=8)
config._attn_implementation='sdpa'
model=Qwen3ForCausalLM(config).double().eval()
for parameter in model.parameters():parameter.requires_grad_(False)
h=torch.randn(2,8,32,dtype=torch.float64,requires_grad=True)
rotary=model.model.rotary_emb(h,torch.arange(8).unsqueeze(0))
target=torch.randint(0,64,(2,7))
def loss(x):
    x=block_forward(model.model.layers[1],x,rotary)
    logits=model.lm_head(model.model.norm(x))
    return cross_entropy(logits[:,:-1,:].reshape(-1,64),target.reshape(-1))
gradient=torch.autograd.grad(loss(h),h)[0]
direction=torch.randn_like(h)
direction/=direction.norm()
autograd=float((gradient*direction).sum())
# Native RMSNorm deliberately casts internally to float32 even for double inputs.
# At epsilon=1e-4 finite differences amplify that rounding. Use a resolved step,
# record the mismatch, and do not claim double-precision verification of RMSNorm.
epsilon=.1
numerical=float((loss(h.detach()+epsilon*direction)-loss(h.detach()-epsilon*direction))/(2*epsilon))
assert abs(autograd-numerical)<1e-7,(autograd,numerical)
with torch.no_grad():
    ids=torch.randint(0,64,(2,8));changed=ids.clone();changed[:,4:]=(changed[:,4:]+1)%64
    original=model.model(ids,use_cache=False).last_hidden_state
    altered=model.model(changed,use_cache=False).last_hidden_state
    assert torch.equal(original[:,:4],altered[:,:4])
print('PASS suffix directional derivative:',autograd,numerical,'; causal prefix invariant')
