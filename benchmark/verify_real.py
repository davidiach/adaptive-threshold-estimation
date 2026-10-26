"""Finite-tape coupling checks against an independent scalar classifier."""
from __future__ import annotations
import itertools
import json
import math
import sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
if (ROOT/'.runtime/python').exists():sys.path.insert(0,str(ROOT/'.runtime/python'))
import numpy as np
from real_threshold import tape_pair, antithetic_tape, sum_tape, real_estimate, real_replicates, level_count
from reference import seed_rng


def reference_single(tape,cap,threshold,minimum):
    n=1
    while True:
        sample=tape[:n]
        mean=float(sample.mean())
        if n==cap:return int(mean>0),n
        if n>=minimum:
            bound=threshold*math.sqrt(float(sample.var(ddof=1))*(1+math.log(cap/n))/n)
            if abs(mean)>bound:return int(mean>0),n
        n*=2


def verify():
    rng=np.random.default_rng(2026102603)
    checks=0
    # Exhaust all short ternary tapes, including exact ties and zero variance.
    tapes=(np.asarray(t,dtype=float) for t in itertools.product([-1,0,1],repeat=8))
    for tape in tapes:
        for threshold in [0.,.5,2.]:
            for j in range(3):
                start,ratio,minimum=2,2,2
                cap=start*ratio**j
                fine,wf=reference_single(tape,cap,threshold,minimum)
                coarse,wc=(0,0) if j==0 else reference_single(tape,cap//ratio,threshold,minimum)
                actual,work=tape_pair(tape,j,start,ratio,threshold,minimum)
                assert actual==fine-coarse and work==max(wf,wc)
                assert 1<=work<=cap
                checks+=1
    # Longer unbounded-valued tapes exercise the production minimum checkpoint.
    for _ in range(1000):
        tape=rng.standard_t(3,size=256)+rng.uniform(-2,2)
        threshold=float(rng.choice([.5,1.,1.5]))
        increments=[]
        for j in range(5):
            cap=16*2**j
            fine,wf=reference_single(tape,cap,threshold,16)
            coarse,wc=(0,0) if j==0 else reference_single(tape,cap//2,threshold,16)
            actual,work=tape_pair(tape,j,16,2,threshold,16)
            assert actual==fine-coarse and work==max(wf,wc)
            increments.append(actual)
            checks+=1
        top,_=reference_single(tape,256,threshold,16)
        assert sum(increments)==top
        p=np.array([.2,.3,.1,.15,.25])
        assert abs(float(p@(np.asarray(increments)/p))-top)<1e-12
        sum_values=[]
        individual=[reference_single(tape,16*2**j,threshold,16) for j in range(5)]
        for j in range(5):
            actual,work=sum_tape(tape,j,16,2,threshold,p)
            expected=individual[0][0]+sum((individual[k][0]-individual[k-1][0])/p[k:].sum() for k in range(1,j+1))
            assert abs(actual-expected)<1e-12
            assert work==max(w for z,w in individual[:j+1])
            sum_values.append(actual)
            checks+=1
        assert abs(float(p@np.asarray(sum_values))-top)<1e-12
        for ratio in [2,4]:
            fine,wf=reference_single(tape,256,threshold,16)
            coarse=[reference_single(tape[k::ratio],256//ratio,threshold,16) for k in range(ratio)]
            delta,work=antithetic_tape(tape,1,256//ratio,ratio,threshold,16)
            assert delta==fine-sum(z for z,w in coarse)/ratio
            assert work==max(wf,ratio*max(w for z,w in coarse))
            checks+=1
    for b in [16384,65536]:
        for s in [16,64,256]:
            for ratio in [2,4]:
                assert 4*s*ratio**(level_count(b,s,ratio)-1)<=b
    for seed in range(8327,8337):
        p=np.array([.8,.2]);seed_rng(seed)
        separate=[real_estimate(64,4,1.,p,False,True) for _ in range(4)]
        seed_rng(seed)
        v,c=real_replicates(64,4,1.,p,1,False,True,4)
        assert v[0]==sum(a for a,b in separate)/4
        assert c[0]==sum(b for a,b in separate)
    out=dict(passed=True,finite_tape_pair_checks=checks,exact_telescope_checks=1000,
             repeated_calibration_checks=10,seed=2026102603,scope='implementation coupling and cost invariants; not a statistical error theorem')
    (ROOT/'results/real_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))


if __name__=='__main__':verify()
