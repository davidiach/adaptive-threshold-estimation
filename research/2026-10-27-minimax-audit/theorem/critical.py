"""Reference implementation and exact finite diagnostics for critical.tex.

The floating-point likelihood implementation is not a certified implementation
of real comparisons. Exact Fraction diagnostics below certify only their finite
instances. This module runs no unbounded sampling or benchmark by default.
"""
from __future__ import annotations

from fractions import Fraction as F
from math import ceil, log, log1p, log2, comb, isfinite
import json
from pathlib import Path


def plan(a: float, rho: float, j: int) -> tuple[float, int, int]:
    if not (0 < a <= .5 and 0 < rho <= .25 and isinstance(j, int) and j >= 0):
        raise ValueError("Require 0<a<=1/2, 0<rho<=1/4, integer j>=0")
    epsilon = 16.0 ** (-(j + 1))
    if epsilon == 0:
        raise OverflowError("Floating-point plan cannot represent epsilon")
    n = ceil(1 / (a * a * rho * epsilon))
    k = ceil(log2(a) + .5 * log2(n))
    return epsilon, n, k


def classifier(flip, a: float, rho: float, epsilon: float, cap: int):
    """One finite capped classifier; flip() returns next bit of the SAME coin.

    Cost returned is every requested bit. This is a float reference, not a
    roundoff-controlled realization of the mathematical boundary.
    """
    if not (0 < a <= .5 and 0 < rho <= .25 and 0 < epsilon <= 1 and cap >= a**-2):
        raise ValueError("Invalid classifier inputs")
    kmax = ceil(log2(a) + .5 * log2(cap))
    refs = [a * 2.0 ** (-(k + 1)) for k in range(kmax + 1)]
    plus = [log(1 + 2*r) for r in refs]
    minus = [log(1 - 2*r) for r in refs]
    neg_bound = log(kmax + 1) - log(epsilon)
    pos_bound = neg_bound - log(rho)
    heads = 0
    for n in range(1, cap + 1):
        bit = flip()
        if bit not in (0, 1):
            raise ValueError("Observation must be a bit")
        heads += bit
        if n == cap:
            return int(2 * heads > n), n
        if any(heads*m + (n-heads)*p >= neg_bound for p,m in zip(plus,minus)):
            return 0, n
        if any(heads*p + (n-heads)*m >= pos_bound for p,m in zip(plus,minus)):
            return 1, n
    raise AssertionError("Finite cap must terminate")


def increment(flip, a: float, rho: float, j: int):
    """Two successive blocks of one coin; do not replace flip between calls."""
    eps, cap, _ = plan(a, rho, j)
    fine, work = classifier(flip, a, rho, eps, cap)
    if j == 0:
        return fine, work
    eps, cap, _ = plan(a, rho, j-1)
    coarse, extra = classifier(flip, a, rho, eps, cap)
    return fine-coarse, work+extra


def bounded_classifier(observe, a: float, rho: float, epsilon: float, cap: int):
    """Direct [0,1] e-process classifier; real observations are not converted.

    Float comparisons are not certified real-number comparisons. observe()
    must supply conditionally iid observations of one retained hidden state.
    """
    if not (0<a<=.5 and 0<rho<=.25 and 0<epsilon<=1 and cap>=a**-2):
        raise ValueError("Invalid classifier inputs")
    kmax=ceil(log2(a)+.5*log2(cap))
    refs=[a*2.0**(-(k+1)) for k in range(kmax+1)]
    log_plus=[0.0]*(kmax+1)
    log_minus=[0.0]*(kmax+1)
    neg_bound=log(kmax+1)-log(epsilon)
    pos_bound=neg_bound-log(rho)
    total=0.0
    for n in range(1,cap+1):
        x=observe()
        if not isfinite(x) or not 0<=x<=1:
            raise ValueError("Observation must be in [0,1]")
        total+=x
        if n==cap:
            return int(2*total>n),n
        for k,r in enumerate(refs):
            log_plus[k]+=log1p(2*r*(2*x-1))
            log_minus[k]+=log1p(-2*r*(2*x-1))
        if max(log_minus)>=neg_bound:
            return 0,n
        if max(log_plus)>=pos_bound:
            return 1,n
    raise AssertionError("Finite cap must terminate")


def exact_classifier(a: F, rho: F, eps: F, cap: int, d: F, sign: int):
    """Full finite decision-tree probability calculation with exact rationals."""
    kmax = 0
    while F(4) ** kmax < a*a*cap:
        kmax += 1
    refs = [a/F(2)**(k+1) for k in range(kmax+1)]
    p = F(1,2)+(2*sign-1)*d
    alive = {0:F(1)}
    answer = [F(0),F(0)]
    wrong_cross = F(0)
    work = F(0)
    for n in range(1,cap+1):
        work += sum(alive.values())
        after = {}
        for heads, mass in alive.items():
            for bit,prob in ((0,1-p),(1,p)):
                h = heads+bit
                weight = mass*prob
                if not weight:
                    continue
                decision = None
                if n == cap:
                    decision = int(2*h>n)
                elif any((1-2*r)**h*(1+2*r)**(n-h) >= (kmax+1)/eps for r in refs):
                    decision = 0
                elif any((1+2*r)**h*(1-2*r)**(n-h) >= (kmax+1)/(rho*eps) for r in refs):
                    decision = 1
                if decision is None:
                    after[h] = after.get(h,F(0))+weight
                else:
                    answer[decision] += weight
                    if n < cap and decision != sign:
                        wrong_cross += weight
        alive = after
    majority_error = sum(F(comb(cap,h))*p**h*(1-p)**(cap-h)
                         for h in range(cap+1) if int(2*h>cap) != sign)
    allowance = eps if sign else rho*eps
    assert not alive and sum(answer)==1
    assert wrong_cross <= allowance
    assert answer[1-sign] <= allowance+majority_error
    assert 1 <= work <= cap
    return {"a":str(a),"rho":str(rho),"epsilon":str(eps),"cap":cap,
            "gap":str(d),"sign":sign,"error_exact":str(answer[1-sign]),
            "wrong_cross_exact":str(wrong_cross),"work_exact":str(work),
            "majority_error_exact":str(majority_error)}


def exact_psi_fixture(gaps, masses, t, h):
    w = [min(F(1),(t/d)**2) for d in gaps]
    rho = sum(m*v for m,v in zip(masses,w))
    # sqrt(w) is rational for these deliberately rational-cutoff instances.
    value = sum(m*min(v,h*min(F(1),t/d)/d) for d,m,v in zip(gaps,masses,w))
    if h >= t:
        split = rho
    else:
        split = sum(m for d,m in zip(gaps,masses) if d<=h)
        split += h*sum(m/d for d,m in zip(gaps,masses) if h<d<=t)
        split += h*t*sum(m/d**2 for d,m in zip(gaps,masses) if d>t)
    assert value==split
    assert 0<rho<=F(1,4)
    return {"gaps":list(map(str,gaps)),"masses":list(map(str,masses)),
            "t":str(t),"h":str(h),"rho":str(rho),"psi_exact":str(value),
            "w":list(map(str,w))}


def run_checks():
    finite=[]
    for cap in (8,16,32):
        for d in (F(1,64),F(1,8),F(1,2)):
            for sign in (0,1):
                for rho in (F(1,4),F(1,16)):
                    finite.append(exact_classifier(F(1,2),rho,F(1,4),cap,d,sign))
    atomic=[]
    for h in (F(1,128),F(1,32),F(1,16),F(1,8)):
        atomic.append(exact_psi_fixture([F(1,32),F(1,4)],[F(1,16),F(15,16)],F(1,16),h))
        atomic.append(exact_psi_fixture([F(1,64),F(1,8),F(1,2)],
                       [F(1,32),F(7,32),F(3,4)],F(1,32),h))
    old_counter=[]
    for root in (4,8,16):
        rho=F(1,root*root)
        heuristic=rho*rho+4*(1-rho)*rho*rho/F(root)
        old_counter.append({"rho":str(rho),"h":str(rho*rho),
                            "psi_exact":str(rho),"old_heuristic_exact":str(heuristic),
                            "separation_exact":str(rho/heuristic)})
    # Closed geometric sums, evaluated in rational arithmetic.
    second=F(35,16)+F(85,16)*F(1,7)
    assert second==F(165,56) and second<4
    # Test the reference state machine at deterministic endpoints/ties.
    assert classifier(lambda:0,.5,.25,.25,32)==(0,7)
    assert classifier(lambda:1,.5,.25,.25,32)==(1,10)
    tape=iter([0,1]*4)
    assert classifier(lambda:next(tape),.5,.25,.25,8)==(0,8)
    for fixed in (0.0,1.0):
        assert bounded_classifier(lambda:fixed,.5,.25,.25,32)==classifier(lambda:int(fixed),.5,.25,.25,32)
    tape=iter([.25,.75]*4)
    assert bounded_classifier(lambda:next(tape),.5,.25,.25,8)==(0,8)
    output={"status":"NUMERICAL: exact rational finite diagnostics, not a universal proof",
            "seed":None,"arithmetic":"fractions.Fraction exact rational; float state-machine endpoint checks",
            "finite_classifier_cases":finite,"atomic_psi_cases":atomic,
            "preserved_heuristic_counterexample":old_counter,
            "second_moment_coefficient_exact":str(second),
            "limits":"Finite caps 8,16,32; no unrestricted minimax computation, no infinite-horizon certificate."}
    path=Path(__file__).with_name("critical_checks.json")
    path.write_text(json.dumps(output,indent=2)+"\n")
    print(json.dumps({"finite_classifier_cases":len(finite),"atomic_psi_cases":len(atomic),
                      "counterexample_cases":len(old_counter),"second_moment_coefficient":str(second),
                      "result":str(path)}))


if __name__=="__main__":
    run_checks()
