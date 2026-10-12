from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from design import choose,step_optimism
c=[{'alpha':0.,'selection_nll':[3.,3.],'selection_mse':[1.,1.]},
 {'alpha':.5,'selection_nll':[2.,2.],'selection_mse':[2.,2.]},
 {'alpha':1.,'selection_nll':[2.,2.],'selection_mse':[3.,3.]}]
assert choose('task_select',c)[0]==1 and choose('local_select',c)[0]==0
for v in c:v['audit_nll']=[-9999*v['alpha']]*8
assert choose('task_select',c)[0]==1 and choose('local_select',c)[0]==0
r={'chosen_alpha':.5,'candidates':[{'alpha':0.,'selection_nll':[4.,6.],'audit_nll':[3.,5.]},
 {'alpha':.5,'selection_nll':[3.,5.],'audit_nll':[3.,4.]}]}
assert step_optimism(r)=={'selection_gain':1.,'audit_gain':.5,'optimism':.5}
print('PASS: selector objective separation, deterministic tie, audit immunity, paired optimism sign')
