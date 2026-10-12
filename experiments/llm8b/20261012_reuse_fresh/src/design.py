"""Selection is deliberately unable to receive audit scores."""
import math,statistics

def choose(policy,candidates):
 field='selection_nll' if policy=='task_select' else 'selection_mse'
 scores=[statistics.mean(c[field]) for c in candidates]
 assert all(math.isfinite(s) for s in scores)
 index=min(range(len(candidates)),key=lambda i:(scores[i],candidates[i]['alpha']))
 return index,scores

def step_optimism(record):
 zero=next(c for c in record['candidates'] if c['alpha']==0.)
 chosen=next(c for c in record['candidates'] if c['alpha']==record['chosen_alpha'])
 sg=statistics.mean(zero['selection_nll'])-statistics.mean(chosen['selection_nll'])
 ag=statistics.mean(zero['audit_nll'])-statistics.mean(chosen['audit_nll'])
 return {'selection_gain':sg,'audit_gain':ag,'optimism':sg-ag}
