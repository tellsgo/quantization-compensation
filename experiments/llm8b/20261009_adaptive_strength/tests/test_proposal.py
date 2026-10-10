from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from proposal import coefficient,neighbor,choose
assert coefficient(2.,4.,1.)==(0.5,False)
assert coefficient(-1.,2.,1.)==(0.,False)
assert coefficient(4.,2.,1.)==(1.,False)
assert coefficient(0.,0.,1.)==(0.,True)
assert coefficient(1e-20,1e-20,1.)==(0.,True)
assert neighbor(1.)==.9 and neighbor(0.)==.1 and neighbor(.5)==.6
assert choose([{'alpha':.5,'loss':1.},{'alpha':0.,'loss':1.}])['alpha']==0.
# Convex quadratic with residual [1,2], direction [2,0] has constrained minimum 1/2.
a,_=coefficient(2,4,5)
for b in [0,.25,.5,.75,1]:assert (1-2*a)**2+4<=(1-2*b)**2+4
print('PASS: known quadratic, clipping, degenerate direction, neighbor, deterministic tie')
