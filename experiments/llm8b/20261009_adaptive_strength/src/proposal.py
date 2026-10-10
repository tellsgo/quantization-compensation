"""Pure proposal and selection rules; no diagnostic data enters them."""
def coefficient(dot,energy,target_energy,relative=1e-12):
 if energy<=relative*max(target_energy,1e-30):return 0.,True
 return min(1.,max(0.,dot/energy)),False

def neighbor(alpha,step=.1):return min(1.,max(0.,alpha+step if alpha<=.5 else alpha-step))

def choose(scores):return min(scores,key=lambda row:(row['loss'],row['alpha']))
