from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from analyze import spearman
assert spearman([1,2,3],[4,5,6])==1
assert spearman([1,2,3],[6,5,4])==-1
assert spearman([1,1,1],[1,2,3]) is None
assert spearman([1,1,2],[3,3,4])==1
print('PASS: Spearman increasing, decreasing, constant and ties')
