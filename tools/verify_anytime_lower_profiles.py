"""Exact finite regression examples for the paper lower-bound profiles.

Includes grid atoms; this finite check does not prove the all-law theorem.
"""

from fractions import Fraction as F
from itertools import product
from random import Random

rng=Random(20261105)
tau=F(1,8)
rho=F(1,4)
checks=0
for case in range(16):
 gaps=[tau/F(4)**i for i in [0,1,2,4,9,24]]
 if case:
  gaps += [tau*F(rng.randint(1,31),32)/F(4)**rng.randint(0,20) for _ in range(5)]
 weights=[F(rng.randint(1,40)) for _ in gaps]
 weights=[w/sum(weights)*rho/2 for w in weights]
 def eps(j):return tau/F(4)**j
 def tail(j,d):
  k=j
  while eps(k)>=d:k+=1
  return F(4,3)*eps(k)/d
 def W(j):return sum(w*tail(j,d) for d,w in zip(gaps,weights))
 for j in range(32):
  t=sum(w*min(F(1),eps(j)/d) for d,w in zip(gaps,weights))
  assert t/3<=W(j)<=4*t/3
  assert W(j+1)>=W(j)/4
  checks+=2
 boundaries=[0]
 for _ in range(5):
  j=boundaries[-1]+1
  while W(j)>W(boundaries[-1])/4:j+=1
  assert W(boundaries[-1])/16<W(j)<=W(boundaries[-1])/4
  boundaries.append(j)
 words=list(product([0,1],repeat=5))
 priors={}
 means={}
 for v in words:
  q=[F(1,4)+F(3,128)*sum(v[k]*(tail(boundaries[k],d)-tail(boundaries[k+1],d)) for k in range(5)) for d in gaps]
  assert all(F(1,4)<=x<=F(9,32) for x in q)
  assert sum(w*x for w,x in zip(weights,q))<=rho
  priors[v]=q
  means[v]=sum(w*x for w,x in zip(weights,q))
 for v in words:
  for u in words:
   if v==u:continue
   k=next(i for i in range(5) if v[i]!=u[i])
   assert abs(means[v]-means[u])>=F(3,256)*W(boundaries[k])
   assert all(d*abs(a-b)<=eps(boundaries[k])/32 for d,a,b in zip(gaps,priors[v],priors[u]))
   checks+=2
print(checks,'exact rational checks across 16 atomic examples, including grid endpoints')
