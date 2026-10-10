import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from analyze import assess

def make(old,new,diag_old=None,diag_new=None):
 return {'layer':0,'group':0,'terminal_control':False,'candidates':[
 {'alpha':a,'select':{'rtn':x,'completed':y},'diag':{'rtn':dx,'completed':dy}} for a,x,y,dx,dy in
 zip([0.,.5,1.],old,new,diag_old or old,diag_new or new)]}
r=assess(make([1,2,3],[3,2,1]));assert r['robust_switch'] and r['diagnostic_reversal'] and r['completed_regret']==2 and r['strict_pair_inversions']==3
r=assess(make([1,2,3],[3,2,1],[1,2,3],[1,2,3]));assert r['robust_switch'] and not r['diagnostic_reversal'] and r['diagnostic_completed_gain']==-2
r=assess(make([1,1,2],[1,1,2]));assert not r['raw_switch']
r=assess(make([1,1.000001,2],[1.000001,1,2]));assert r['raw_switch'] and not r['robust_switch']
r=assess(make([1,2,3],[11,12,13]));assert not r['raw_switch'] and r['strict_pair_inversions']==0
print('PASS: rank reversal, independent-data rejection, ties, near-ties, suffix additive offset')
