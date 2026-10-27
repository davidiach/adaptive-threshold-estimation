"""Exact rational finite-support and majority-channel diagnostics, not minimax proofs."""
from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
import json

def main():
    laws=[([F(1,4)],[F(1)]),([F(1,1000),F(1,2)],[F(1,100),F(99,100)]),
          ([F(1,1024),F(1,16),F(1,2)],[F(1,100),F(19,100),F(4,5)])]
    rows=[];checks=0
    for ds,ps in laws:
        t=F(1,1000)
        ws=[min(F(1),t*t/(d*d)) for d in ds]
        rho=sum(p*w for p,w in zip(ps,ws));assert 0<rho<=F(1,4)
        for h in [t/10,t,2*t]:
            candidate=sum(p*min(w,h*min(F(1),t/d)/d) for p,d,w in zip(ps,ds,ws))
            formula=rho if h>=t else sum(p*(1 if d<=h else h/d if d<=t else h*t/(d*d)) for p,d in zip(ps,ds))
            assert candidate==formula
            valid=0
            for ks in product(range(21),repeat=len(ds)):
                w=[F(k*k,400) for k in ks]
                if sum(p*x for p,x in zip(ps,w))>rho:continue
                value=sum(p*min(x,h*F(k,20)/d) for p,d,x,k in zip(ps,ds,w,ks))
                assert value<=candidate;valid+=1;checks+=1
            rows.append(dict(gaps=list(map(str,ds)),mass=list(map(str,ps)),rho=str(rho),h=str(h),value=str(candidate),feasible_grid_points=valid))
    channel=0
    for d in [F(1,100),F(1,4),F(1,2)]:
        for m in [1,3,5,11]:
            prob=lambda p:sum(F(comb(m,k))*p**k*(1-p)**(m-k) for k in range(m//2+1,m+1))
            f=prob(F(1,2)-d);s=prob(F(1,2)+d);assert s==1-f
            for theta in [F(0),F(1,100),F(1,4)]:
                p=f+(1-2*f)*theta;assert (p-f)/(1-2*f)==theta;channel+=1
    out=dict(status='certified exact rational finite calculations; not an unrestricted minimax or optimizer proof',rows=rows,grid_comparisons=checks,majority_identity_checks=channel,seed=None)
    path=Path(__file__).with_name('EXACT_CHECKS.json');path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='rows'}))

if __name__=='__main__':main()
