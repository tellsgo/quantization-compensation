"""Exact evaluator for three fixed finite-support witnesses; no search."""
from fractions import Fraction as Q
from math import isqrt
import itertools

def T(M):return list(map(list,zip(*M)))

def mm(A,B):return [[sum(x*y for x,y in zip(r,c)) for c in zip(*B)] for r in A]

def add(A,B):return [[x+y for x,y in zip(r,s)] for r,s in zip(A,B)]

def scale(A,s):return [[x*s for x in r] for r in A]

def sub(A,B):return add(A,scale(B,-1))

def zero(n):return [[Q(0) for _ in range(n)] for _ in range(n)]

def gram(A):return mm(A,T(A))

def relu(A):return [[max(x,0) for x in r] for r in A]

def trace(A):return sum(A[i][i] for i in range(len(A)))

def inv(A):
 n=len(A); B=[list(r)+[Q(i==j) for j in range(n)] for i,r in enumerate(A)]
 for j in range(n):
  k=next(i for i in range(j,n) if B[i][j]);B[k],B[j]=B[j],B[k];p=B[j][j];B[j]=[x/p for x in B[j]]
  for i in range(n):
   if i!=j:
    q=B[i][j];B[i]=[x-q*y for x,y in zip(B[i],B[j])]
 return [r[n:] for r in B]

def sqrt_bounds(x):
 assert x>=0
 den=10**40; v=isqrt(x.numerator*den*den//x.denominator);lo=Q(v,den);hi=lo if lo*lo==x else Q(v+1,den)
 assert lo*lo<=x<=hi*hi
 return lo,hi

def comm_norm_bounds(P,c):
 comp=[j for j in range(len(P)) if j not in c];B=[[P[i][j] for j in comp] for i in c]
 if not B or not comp:return Q(0),Q(0)
 if len(B)>len(comp):B=T(B)
 S=gram(B)
 if len(S)==1:return sqrt_bounds(S[0][0])
 assert len(S)==2
 a,b,d=S[0][0],S[0][1],S[1][1];lo,hi=sqrt_bounds((a-d)**2+4*b*b)
 return sqrt_bounds(max(Q(0),(a+d+lo)/2))[0],sqrt_bounds((a+d+hi)/2)[1]

def evaluate(cfg,paper_first=True):
 X0=[[Q(x) for x in r] for r in cfg['X1']];Ws=[[[Q(x) for x in r] for r in M] for M in cfg['Ws']];amps=[[[Q(x) for x in r] for r in M] for M in cfg['amps']];alpha=list(map(Q,cfg['a']));L=len(Ws)
 X=[X0];pre=[]
 for W in Ws:pre.append(mm(W,X[-1]));X.append(relu(pre[-1]))
 groups={}
 for j in range(len(X0[0])):groups.setdefault(tuple(x[i][j]>0 for x in pre for i in range(len(x))),[]).append(j)
 cells=list(groups.values()); C=len(cells)
 noises=[]
 for M in amps:
  coords=[(i,j) for i in range(len(M)) for j in range(len(M[0])) if M[i][j]];es=[]
  for signs in itertools.product([-1,1],repeat=len(coords)):
   E=[[Q(0) for _ in r] for r in M]
   for (i,j),s in zip(coords,signs):E[i][j]=s*M[i][j]
   es.append(E)
  noises.append(es)
 sources=[[[zero(len(X[l])) for _ in cells] for l in range(L)] for b in range(2)]
 expected_k=[[[Q(0) for _ in cells] for l in range(L)] for b in range(2)]
 flips=0;states=0;ms={}
 for scheme in ['Q','B']:
  paths=[(X0,Q(1))]
  for l in range(L):
   nextp=[]
   for Z,p in paths:
    R=sub(Z,X[l]);RR=gram(R);P=None
    if scheme=='Q' and alpha[l]: inv(gram(Z)) # required legality, including layer 1
    if scheme=='Q' and alpha[l] and (l>0 or not paper_first):
     P=mm(mm(T(Z),inv(gram(Z))),Z)
     for c,idx in enumerate(cells):
      for b,k in enumerate(comm_norm_bounds(P,idx)):
       sources[b][l][c]=add(sources[b][l][c],scale(RR,p*k));expected_k[b][l][c]+=p*k
    Ztarget=Z if scheme=='B' or not alpha[l] or l==0 else add(scale(Z,1-alpha[l]),scale(mm(X[l],P),alpha[l]))
    base=mm(Ws[l],Ztarget)
    for E in noises[l]:
     zz=add(base,mm(E,Z));flips+=sum((zz[i][j]>0)!=(pre[l][i][j]>0) for i in range(len(zz)) for j in range(len(zz[0])))
     nextp.append((relu(zz),p/len(noises[l])))
   paths=nextp
  states=len(paths);ms[scheme]=sum(p*trace(gram(sub(Z,X[-1]))) for Z,p in paths)
 def psi(l,M,D):return [[sum(amps[l][i][j]**2*M[j][j] for j in range(len(M)))*D[i] if i==k else Q(0) for k in range(len(D))] for i in range(len(D))]
 bound=[];nopsi=[]
 for b in range(2):
  total=Q(0);bad=Q(0)
  for c,idx in enumerate(cells):
   K=zero(len(X0));V=zero(len(X0));Kbad=zero(len(X0))
   for l in range(L):
    D=[int(pre[l][i][idx[0]]>0) for i in range(len(Ws[l]))];F=[[D[i]*x for x in r] for i,r in enumerate(Ws[l])]
    Aterm=scale(mm(mm(F,sources[b][l][c]),T(F)),alpha[l]);Bterm=scale(mm(mm(F,gram(X[l])),T(F)),alpha[l]*expected_k[b][l][c]);pv=psi(l,V,D)
    K=add(add(mm(mm(F,K),T(F)),pv),Aterm);Kbad=add(mm(mm(F,Kbad),T(F)),Aterm)
    V=add(add(scale(mm(mm(F,V),T(F)),1-alpha[l]),pv),Bterm)
   total+=trace(K);bad+=trace(Kbad)
  bound.append(total);nopsi.append(bad)
 ex=ms['Q']-ms['B']
 return {'support_states_per_scheme':states,'flips':flips,'all_required_Gram_inversions_exact':True,'mseB':str(ms['B']),'mseQ':str(ms['Q']),'excess':str(ex),'bound_interval':[str(x) for x in bound],'no_psi_bound_interval':[str(x) for x in nopsi],'ratio_interval':[float(ex/bound[1]),float(ex/bound[0])] if bound[0]>0 else None,'certifies_no_violation':ex<=bound[0],'certifies_omitted_psi_violation':ex>nopsi[1],'paper_first_layer_zero':paper_first,'cells':cells}

