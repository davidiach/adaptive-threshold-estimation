"""Reproducible v4 diagnostics; none of these finite checks is a proof.

Runs symbolic identities, high-precision predictive and Hellinger comparisons,
floating-point dynamic programs (not Monte Carlo), modulus formula checks,
calibration Monte Carlo diagnostics, and API smoke/validation tests.
"""
from __future__ import annotations
import csv
import json
import math
import platform
from dataclasses import asdict
from pathlib import Path

import mpmath as mp
import numpy as np
import scipy
import sympy as sp
from scipy.integrate import quad

from calibration import calibrate, estimate_budget, estimate_confidence
from threshold import R, LEVEL_P, omega_power, omega_log
from verify import pair_dp

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'results'
OUT.mkdir(exist_ok=True)


def symbolic_checks() -> list[str]:
    e, L = sp.symbols('eta L', positive=True)
    a, b = sp.Rational(1, 2)+e, sp.Rational(1, 2)-e
    rp, rm = a*L/(b+a*L), b*L/(a+b*L)
    target=2*e*L/(L+(sp.Rational(1,4)-e**2)*(L-1)**2)
    assert sp.cancel(rp-rm-target)==0
    assert sp.cancel(rm*(1-rm)-a*b*L/(a+b*L)**2)==0
    r=sp.symbols('r', positive=True)
    g=sp.log(r)-2*(r-1)/(r+1)
    assert sp.simplify(sp.diff(g,r)-(r-1)**2/(r*(r+1)**2))==0
    p=sp.symbols('p', positive=True)
    x=sp.symbols('x', real=True)
    # NB(2,p): (k-1) cancels from E[1/(K-1)] and the geometric sum is p.
    assert sp.simplify(p**2/(1-(1-p))-p)==0
    z, cutoff=sp.symbols('z cutoff', positive=True)
    inverse=z/(2*sp.sqrt(1+z**2))
    assert sp.simplify(sp.diff(inverse,z)/cutoff-1/(2*cutoff*(1+z**2)**sp.Rational(3,2)))==0
    d,q=sp.symbols('d q', positive=True)
    px=sp.Rational(1,2)-d+2*d*q
    ey=px*(sp.Rational(1,2)+d)/(2*d)+(1-px)*(-sp.Rational(1,2)+d)/(2*d)
    assert sp.simplify(ey-q)==0
    variance=sp.simplify(px*(1-px)/(4*d**2))
    assert sp.simplify(variance.subs(q,sp.Rational(1,2))-1/(16*d**2))==0
    return ['posterior contrast', 'posterior variance', 'symmetric-KL pointwise derivative',
            'NB two-success inverse moment', 'normalized-magnitude density',
            'fixed-gap unbiasedness', 'fixed-gap sharp variance']


def kl(u, v):
    if u==v:
        return mp.mpf(0)
    if v==0 or v==1:
        return mp.inf
    out=mp.mpf(0)
    if u:
        out+=u*mp.log(u/v)
    if u<1:
        out+=(1-u)*mp.log((1-u)/(1-v))
    return out


def information_checks():
    mp.mp.dps=120
    count=hard_count=hc=0
    maximum=mp.mpf(0); hardmax=mp.mpf(0); hellmax=mp.mpf(0)
    for ds in ['0.000001','0.001','0.01','0.1','0.25','0.49','0.5']:
        d=mp.mpf(ds)
        for es in ['0.00000001','0.001','0.03','0.125','0.24']:
            e=mp.mpf(es); a,b=mp.mpf('.5')+e,mp.mpf('.5')-e
            for exponent in [-60,-20,-5,-1,0,1,5,20,60]:
                L=mp.exp(exponent)
                rp=a*L/(b+a*L); rm=b*L/(a+b*L)
                pp=mp.mpf('.5')-d+2*d*rp; pm=mp.mpf('.5')-d+2*d*rm
                bound=32*d*d*e*e/(1-4*e*e)**2
                for value in [kl(pp,pm),kl(pm,pp)]:
                    assert value>=-mp.mpf('1e-60')
                    ratio=value/bound
                    assert ratio<=1+mp.mpf('1e-50'), (ds,es,exponent,ratio)
                    maximum=max(maximum,ratio);count+=1
                # Stable squared-distance form avoids subtracting nearly equal unit values.
                delta=pp-pm
                H2=delta**2/2*(1/(mp.sqrt(pp)+mp.sqrt(pm))**2+1/(mp.sqrt(1-pp)+mp.sqrt(1-pm))**2)
                # Algebraically KL(pp,pm)+KL(pm,pp), without cancellation.
                jeff=delta*(mp.log1p(delta/pm)-mp.log1p(-delta/(1-pm)))
                assert 8*H2<=jeff+mp.mpf('1e-100')
                if jeff>0: hellmax=max(hellmax,8*H2/jeff)
                hc+=1
        for hs in ['0.3','0.03','0.0003','0.00000003']:
            h=mp.mpf(hs);e=min(1,h/d)/8
            a,b=mp.mpf('.5')+e,mp.mpf('.5')-e
            for exponent in [-30,-8,0,8,30]:
                L=mp.exp(exponent)
                pp=mp.mpf('.5')-d+2*d*a*L/(b+a*L)
                pm=mp.mpf('.5')-d+2*d*b*L/(a+b*L)
                for value in [kl(pp,pm),kl(pm,pp)]:
                    assert value<=mp.mpf(128)/225*h*h+mp.mpf('1e-100')
                    hardmax=max(hardmax,value/(h*h));hard_count+=1
    # Endpoint histories have identical predictive probabilities, even when degenerate.
    assert kl(mp.mpf(0),mp.mpf(0))==0
    assert kl(mp.mpf(1),mp.mpf(1))==0
    return {'decimal_digits':120,'predictive_inequalities':count,
            'largest_ratio_to_sharp_predictive_bound':str(maximum),
            'hard_pair_directional_checks':hard_count,'largest_KL_over_h_squared':str(hardmax),
            'symmetric_KL_Hellinger_checks':hc,'largest_8H2_over_Jeffreys':str(hellmax),
            'deterministic_endpoint_checks':2}


def classifier_checks():
    rows=[]; em=vm=wm=tm=mm=0.0
    for d in [.5,.499,.4,.25,.2,.125,.08,.05,.025,.01,.001]:
        for sign in [-1,1]:
            mean=second=work=0.0
            for level in range(12):
                v=pair_dp(level,.5+sign*d)
                weight=LEVEL_P*R**level
                mean+=v['mean_delta'];second+=v['second_delta']/weight
                work+=weight*v['work']
                n=1<<level; normalizer=min(math.sqrt(n),1/d)
                error=abs(v['z_mean']-int(sign>0))
                eb=min(1.,(n*d*d)**-2)
                assert error<=eb+4e-12
                assert second<=85*normalizer+4e-12
                assert work<=149*normalizer+4e-12
                telescoping=abs(mean-v['z_mean'])
                assert telescoping<4e-12
                em=max(em,error/eb);vm=max(vm,second/normalizer);wm=max(wm,work/normalizer)
                tm=max(tm,telescoping);mm=max(mm,v['mass_residual'])
                rows.append(dict(d=d,sign=sign,level=level,cap=n,error=error,error_bound=eb,
                                 second_moment=second,work=work,normalizer=normalizer,
                                 second_ratio=second/normalizer,work_ratio=work/normalizer))
    with (OUT/'v4_classifier_checks.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
    return dict(programs=len(rows),max_cap=2048,magnitudes=11,signs=2,
                largest_error_bound_ratio=em,largest_second_moment_ratio=vm,
                largest_expected_work_ratio=wm,largest_telescoping_residual=tm,
                largest_mass_residual=mm,proved_second_constant=85,proved_work_constant=149)


def formula_checks():
    residual=0.; n=0
    for a in [.25,.5]:
        for alpha in [.3,.5,1.,1.5,2.,3.]:
            for h in [.8*a,.2*a,.02*a,.0002*a]:
                L=math.log(a/h)
                value=h/a*(1+quad(lambda u:math.exp((1-alpha)*u),0,L,epsabs=1e-12,epsrel=1e-12)[0])
                err=abs(value-omega_power(h,alpha,a));assert err<1e-10
                residual=max(residual,err);n+=1
        for beta in [0.,.5,1.,1.5,2.,3.]:
            for h in [.8*a,.2*a,.02*a,.0002*a]:
                L=1+math.log(a/h)
                value=h/a*(1+quad(lambda u:u**(-beta),1,L,epsabs=1e-12,epsrel=1e-12)[0])
                err=abs(value-omega_log(h,beta,a));assert err<1e-10
                residual=max(residual,err);n+=1
    inv=[]
    for ps in ['0.01','0.1','0.3','0.7','1']:
        p=mp.mpf(ps)
        inv.append({'p':ps,'inverse_expectation':str(p*p/(1-(1-p))),
                    'expected_pilot_count':str(2/p)})
        assert mp.almosteq(p*p/(1-(1-p)),p)
    return dict(modulus_comparisons=n,largest_residual=residual,inverse_moment_checks=inv)


def calibration_checks():
    rng=np.random.default_rng(20261026)
    # Rows: probability, value, integer cost. Include zero costs and dependence.
    cases=[('constant_cost',8,[(.5,-1.,4),(.5,3.,4)]),
           ('correlated',8,[(.25,-2.,0),(.25,1.,1),(.5,4.,8)]),
           ('sparse_cost',16,[(.75,0.,0),(.25,4.,8)]),
           ('deterministic_marker',4,[(.5,-1.,4),(.5,1.,4)])]
    rows=[];reps=4000
    for name,cap,atoms in cases:
        probs=np.array([x[0] for x in atoms]);zs=np.array([x[1] for x in atoms]);cs=np.array([x[2] for x in atoms])
        zeta=float(probs@zs);v=float(probs@((zs-zeta)**2));c=float(probs@cs)
        def draw():
            i=int(rng.choice(len(atoms),p=probs));return float(zs[i]),int(cs[i])
        samples=[calibrate(draw,cap,rng) for _ in range(reps)]
        values=np.array([s.value for s in samples]);works=np.array([s.work for s in samples])
        ev=v*c/cap;ew=4*cap-c
        mean_z=(float(values.mean())-zeta)/(math.sqrt(ev/reps) or 1.)
        work_z=(float(works.mean())-ew)/(float(works.std(ddof=1))/math.sqrt(reps) or 1.)
        # Loose reproducibility sanity checks, not a theorem verification or statistical test suite.
        assert abs(mean_z)<7 and abs(work_z)<7
        rows.append(dict(case=name,repetitions=reps,theoretical_mean=zeta,observed_mean=float(values.mean()),
                         theoretical_variance=ev,observed_variance=float(values.var(ddof=1)),
                         theoretical_work=ew,observed_work=float(works.mean()),
                         mean_standard_error_units=mean_z,work_standard_error_units=work_z,
                         max_observed_work=int(works.max())))
    return rows


def implementation_checks():
    rng=np.random.default_rng(4321)
    def new_coin():
        d=float(rng.choice([.5,.25,.125,.01]));p=.5+(1 if rng.random()<.6 else -1)*d
        return lambda n:int(rng.binomial(n,p))
    outputs=[]
    for B in [1.,3.99,4.,31.999999999999996,32.,128.,1024.]:
        res=estimate_budget(new_coin,B,rng)
        assert math.isfinite(res.value) and res.work>=0
        outputs.append({'budget':B,**asdict(res)})
    outputs.append({'budget':1024,'delta':.1,**asdict(estimate_confidence(new_coin,1024,.1,rng))})
    outputs.append({'budget':1,'delta':.01,**asdict(estimate_confidence(new_coin,1,.01,rng))})
    rejected=0
    for thunk in [lambda:estimate_budget(new_coin,.5,rng),lambda:estimate_budget(new_coin,float('nan'),rng),
                  lambda:estimate_confidence(new_coin,100,0,rng),lambda:estimate_confidence(new_coin,100,.5,rng),
                  lambda:calibrate(lambda:(1,5),4,rng),lambda:calibrate(lambda:(1,0),0,rng)]:
        try: thunk()
        except ValueError:rejected+=1
        else:raise AssertionError('Invalid input was not rejected')
    return dict(smoke_runs=outputs,invalid_inputs_rejected=rejected,
                note='Single runs are smoke tests; the work budget is only an expectation.')


def main():
    result={'scope':'Original proof arguments, supported by these finite diagnostics; no independent review or priority claim.',
            'environment':{'python':platform.python_version(),'numpy':np.__version__,'scipy':scipy.__version__,
                           'sympy':sp.__version__,'mpmath':mp.__version__}}
    for name,fn in [('symbolic',symbolic_checks),('information',information_checks),('classifier',classifier_checks),
                    ('formulas',formula_checks),('calibration_monte_carlo',calibration_checks),('implementation',implementation_checks)]:
        print(f'Running {name} ...',flush=True)
        result[name]=fn()
    (OUT/'v4_verification_summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
