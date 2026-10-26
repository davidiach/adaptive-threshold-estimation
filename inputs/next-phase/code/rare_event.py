"""Reference code for the proved power-margin theorem and the conjectured modulus.

The shifted estimator needs alpha, a and rho. It is NOT a distribution-blind
rare-event theorem. Work guarantees are in expectation, never a hard cap.
Atomic Psi evaluation is exact up to numerical root finding; its general minimax
UPPER interpretation is a conjecture, not a proved guarantee.
"""
from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
from typing import Callable
import math, sys
import numpy as np
from scipy.optimize import brentq
BASE = Path(__file__).resolve().parents[1] / 'baseline/Adaptive_Threshold_v4/code'
sys.path.insert(0, str(BASE))
from calibration import calibrate, Result
from threshold import decision

R = 2.0**(-.5)

@dataclass(frozen=True)
class PowerPlan:
    base: int
    cap: int
    levels: int

def power_plan(budget: float, rho: float, alpha: float, a: float=.25) -> PowerPlan | None:
    if not all(map(math.isfinite, (budget, rho, alpha, a))):
        raise ValueError('All parameters must be finite')
    if budget < 1 or not 0 < rho <= .25 or not 0 < alpha < 2 or not 0 < a <= .25:
        raise ValueError('Require B>=1, 0<rho<=1/4, 0<alpha<2, 0<a<=1/4')
    ke = 4/(4-alpha)
    exponent = math.ceil(-2*math.log2(a) + 2/alpha*math.log2(ke/rho))
    if exponent > math.log2(budget/4):
        return None
    if exponent >= 62:
        raise ValueError('Required cap is too large for this reference implementation')
    base = 1 << exponent
    cap = base; levels = 0
    while 8*cap <= budget:
        cap *= 2; levels += 1
    if cap >= 2**63:
        raise ValueError('Integer calibration supports caps below 2**63')
    return PowerPlan(base, cap, levels)

def shifted_increment(j: int, base: int, count_source: Callable[[int], int]) -> tuple[int,int]:
    if j < 0 or base < 1 or base & (base-1):
        raise ValueError('Require a nonnegative level and dyadic base')
    cap = base << j
    other_cap = 0 if j == 0 else cap//2
    z = None; zc = 0 if j == 0 else None
    n = 1; prev = 0; heads = 0
    while True:
        k = int(count_source(n-prev))
        if not 0 <= k <= n-prev:
            raise ValueError('Invalid observation-count oracle')
        heads += k
        if z is None: z = decision(heads,n,cap)
        if zc is None: zc = decision(heads,n,other_cap)
        if z is not None and zc is not None:
            return z-zc,n
        prev=n; n*=2

def estimate_power(new_coin: Callable[[], Callable[[int],int]], budget: float,
                   rho: float, alpha: float, a: float, rng: np.random.Generator) -> Result:
    """Proved shifted-start construction, with final projection onto [0,rho].

    new_coin returns an independent latent coin's count callback. The algorithm
    does not receive that coin's probability. The power margin must be a valid
    assumption; it is not inferred or certified from the observations.
    """
    plan = power_plan(budget,rho,alpha,a)
    if plan is None: return Result(rho/2,0,0,0)
    def draw():
        j=int(rng.geometric(1-R))-1
        if j>plan.levels:return 0.,0
        z,c=shifted_increment(j,plan.base,new_coin())
        return z/((1-R)*R**j),c
    raw=calibrate(draw,plan.cap,rng)
    return Result(float(np.clip(raw.value,0,rho)),raw.work,raw.pilot_calls,raw.production_calls)

def estimate_power_confidence(new_coin, budget, rho, alpha, a, delta, rng):
    if not math.isfinite(delta) or not 0 < delta <= .25:
        raise ValueError('Require 0<delta<=1/4')
    k=math.ceil((32/9)*math.log(1/delta));k += (k%2==0)
    if budget/k < 1:return Result(rho/2,0,0,0)
    samples=[estimate_power(new_coin,budget/k,rho,alpha,a,rng) for _ in range(k)]
    return Result(float(np.median([v.value for v in samples])),sum(v.work for v in samples),
                  sum(v.pilot_calls for v in samples),sum(v.production_calls for v in samples))

def atomic_psi(d, mass, rho: float, h: float):
    """Return (Psi, cutoff t_rho, optimizing w) for a finite atomic law.

    The variational formula is proved. A matching general minimax upper bound
    is NOT asserted by this function.
    """
    d=np.asarray(d,dtype=float);mass=np.asarray(mass,dtype=float)
    if d.ndim!=1 or d.shape!=mass.shape or not len(d):raise ValueError('Mismatched vectors')
    if np.any(d<=0) or np.any(d>.5) or np.any(mass<=0) or not np.isclose(mass.sum(),1):
        raise ValueError('Require a probability law on (0,1/2] with positive masses')
    if not 0<rho<1 or not math.isfinite(h) or h<0:raise ValueError('Require 0<rho<1, h>=0')
    # Log-coordinate root finding is stable across widely separated magnitudes.
    lo=math.log(float(d.min()))+.5*math.log(rho)-2
    hi=math.log(float(d.max()))
    f=lambda logt: float(mass@np.minimum(1,np.exp(2*(logt-np.log(d)))))-rho
    logt=brentq(f,lo,hi,xtol=1e-13);t=math.exp(logt)
    w=np.minimum(1,(t/d)**2)
    psi=float(mass@np.minimum(w,h*np.sqrt(w)/d))
    return psi,t,w
