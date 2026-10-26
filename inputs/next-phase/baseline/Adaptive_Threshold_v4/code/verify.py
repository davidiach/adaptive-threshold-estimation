"""Legacy v3 checks and joint-classifier recursion. Main v4 runner: verify_v4.py.

These finite-state checks supplement, and do not replace, the proofs.
"""
from __future__ import annotations
import csv, json, math
from pathlib import Path
import numpy as np
import sympy as sp
from scipy.stats import binom
from scipy.signal import convolve
from scipy.integrate import quad
import mpmath as mp
from threshold import R, LEVEL_P, K, decision, omega_power, omega_log, budget_plan

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'results'
OUT.mkdir(exist_ok=True)

def pair_dp(level: int, p: float) -> dict[str, float]:
    """Probability recursion for joint capped classifiers (no Monte Carlo).

    States store stopped decisions, or -1 for a still-active classifier,
    together with the distribution of the shared prefix's success count.
    """
    cap = 1 << level
    cap2 = cap // 2
    states = {(-1, 0 if level == 0 else -1): np.array([1.0])}
    joint = np.zeros((2, 2))
    work = 0.0
    previous = 0
    n = 1
    while states:
        step = n - previous
        pmf = binom.pmf(np.arange(step + 1), step, p)
        work += step * sum(float(v.sum()) for v in states.values())
        nxt = {}
        for (s1, s2), arr in states.items():
            arr2 = convolve(arr, pmf, method='direct')
            for heads, mass in enumerate(arr2):
                if mass == 0:
                    continue
                d1 = decision(heads, n, cap) if s1 == -1 else s1
                d2 = decision(heads, n, cap2) if s2 == -1 else s2
                if d1 is not None and d2 is not None:
                    joint[d1, d2] += mass
                else:
                    key = (-1 if d1 is None else d1, -1 if d2 is None else d2)
                    if key not in nxt:
                        nxt[key] = np.zeros(n + 1)
                    nxt[key][heads] += mass
        states = nxt
        previous = n
        n *= 2
        if n > 2 * cap:
            raise AssertionError('Failed to terminate at cap')
    total = float(joint.sum())
    assert abs(total - 1.0) < 2e-12, total
    z = float(joint[1, :].sum())
    z2 = float(joint[:, 1].sum())
    return {'mean_delta': z - z2, 'second_delta': float(joint[0, 1]+joint[1, 0]),
            'work': work, 'z_mean': z, 'mass_residual': abs(total-1)}

def main():
    eta, ell = sp.symbols('eta ell', positive=True)
    qp = sp.Rational(1, 2) + eta
    qm = sp.Rational(1, 2) - eta
    contrast = qp*ell/(qm+qp*ell)-qm*ell/(qp+qm*ell)
    claimed = 2*eta*ell/(ell+(sp.Rational(1,4)-eta**2)*(ell-1)**2)
    assert sp.cancel(contrast-claimed) == 0

    mp.mp.dps = 70
    kl_max = mp.mpf(0)
    kl_checks = 0
    for ds in ['0.25', '0.1', '0.01', '0.0001']:
        d = mp.mpf(ds)
        for hs in ['0.3', '0.03', '0.003', '0.000003']:
            h = mp.mpf(hs)
            e = mp.mpf(1)/8 * min(1, h/d)
            for exponent in [-30,-12,-4,-1,0,1,4,12,30]:
                L = mp.exp(exponent)
                q1, q0 = mp.mpf('.5')+e, mp.mpf('.5')-e
                r1 = q1*L/(q0+q1*L)
                r0 = q0*L/(q1+q0*L)
                p1 = mp.mpf('.5')-d+2*d*r1
                p0 = mp.mpf('.5')-d+2*d*r0
                kl = p1*mp.log(p1/p0)+(1-p1)*mp.log((1-p1)/(1-p0))
                assert kl >= -mp.mpf('1e-60')
                ratio = kl/(h*h)
                assert ratio <= mp.mpf(4)/3
                kl_max = max(kl_max, ratio)
                kl_checks += 1

    rows = []
    max_error_ratio = max_var_ratio = max_work_ratio = 0.0
    max_telescoping = max_mass = 0.0
    # Include both signs; final ties are deliberately asymmetric.
    for d in [0.25, 0.20, 0.125, 0.08, 0.05, 0.025, 0.01]:
        for sign in [-1, 1]:
            p = 0.5 + sign*d
            mean = second = work = 0.0
            for level in range(11):
                data = pair_dp(level, p)
                prob = LEVEL_P * R**level
                mean += data['mean_delta']
                second += data['second_delta'] / prob
                work += prob * data['work']
                n = 1 << level
                m = min(math.sqrt(n), 1/d)
                error = abs(data['z_mean'] - (1 if sign > 0 else 0))
                err_bound = min(1.0, (n*d*d)**-2)
                assert error <= err_bound + 3e-12
                assert second <= K*m
                assert work <= K*m
                telescoping = abs(mean-data['z_mean'])
                assert telescoping < 3e-12
                max_error_ratio = max(max_error_ratio, error/err_bound)
                max_var_ratio = max(max_var_ratio, second/m)
                max_work_ratio = max(max_work_ratio, work/m)
                max_telescoping = max(max_telescoping, telescoping)
                max_mass = max(max_mass, data['mass_residual'])
                rows.append({'d':d,'sign':sign,'level':level,'cap':n,'classification_error':error,
                    'error_bound':err_bound,'truncated_mean':mean,'truncated_second_moment':second,
                    'truncated_expected_work':work,'normalizer':m,'second_ratio':second/m,'work_ratio':work/m})
    with (OUT/'dynamic_programming_checks.csv').open('w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)

    modulus_residual = 0.0
    modulus_checks = 0
    for alpha in [.3,.5,1.,1.5,2.,3.]:
        for h in [0.2,0.05,0.005,0.00005]:
            # Exact CDF integral identity, integrated in logarithmic coordinates.
            a = .25
            L = math.log(a/h)
            val = h/a + h/a * quad(lambda u: math.exp((1-alpha)*u), 0, L,
                                   epsabs=1e-12, epsrel=1e-12)[0]
            residual = abs(val-omega_power(h,alpha))
            assert residual < 1e-10
            modulus_residual = max(modulus_residual,residual)
            modulus_checks += 1
    for beta in [0.,.5,1.,1.5,2.,3.]:
        for h in [.2,.05,.005,.00005]:
            a=.25; L=1+math.log(a/h)
            val=h/a*(1+quad(lambda u:u**(-beta),1,L,epsabs=1e-12,epsrel=1e-12)[0])
            residual=abs(val-omega_log(h,beta))
            assert residual<1e-10
            modulus_residual=max(modulus_residual,residual)
            modulus_checks+=1

    plan_checks=0
    for budget in [512,1000,10000,1000000,1000000000]:
        for alpha in [.3,.5,1,1.5,3]:
            plan=budget_plan(budget,lambda h:omega_power(h,alpha))
            assert plan is not None
            level,m=plan; h=2**(-level/2); a_h=omega_power(h,alpha)/h
            assert K*m*a_h<=budget*(1+1e-12)
            plan_checks+=1
    summary={
        'posterior_identity':'exact symbolic simplification to zero',
        'predictive_kl_checks_70_decimal_digits':kl_checks,
        'largest_predictive_kl_over_h_squared':str(kl_max),
        'joint_classifier_dynamic_programs':len(rows),
        'largest_classification_error_bound_ratio':max_error_ratio,
        'largest_second_moment_over_truncated_inverse_margin':max_var_ratio,
        'largest_work_over_truncated_inverse_margin':max_work_ratio,
        'proved_common_bound_constant':K,
        'largest_probability_mass_residual':max_mass,
        'largest_telescoping_residual':max_telescoping,
        'modulus_formula_checks':modulus_checks,
        'largest_modulus_formula_residual':modulus_residual,
        'expected_budget_plan_checks':plan_checks,
        'scope':'Deterministic finite-grid diagnostics; not proof, empirical deployment evidence, or independent review.'}
    (OUT/'verification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    main()
