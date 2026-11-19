"""Limits of the Lean proof's method: the call constants that Hoeffding bounds give.

The Lean proof of the constant 12 (UpperCallCost, UpperQuarter) bounds the
padded call cost and the call second moment of one call by Hoeffding's
inequality, union bounds and the exact vote-change probability. This module
evaluates those bounds without the rounding of the certificates, for the
threshold sqrt((a + b*log(cap/n))/n), with v_j = a + b*j*log 2:

* kappa_H: d times the padded cost is at most (1-r)*G(s) for the first grid
  point s in [1, 2) of y_k = 2^k d^2, with G(s) the sum over all integers i of
  sqrt(2^i s)*Phi(2^i s), Phi(y) = sum_{j>=1} r^j sigma_j(y), and sigma_j(y) = 1
  below v_j and exp(-2(sqrt y - sqrt v_j)^2) from v_j on. This regroups the
  per-difference grids of UpperCost by check; the supremum over s is kappa_H.
* sigma_H: d times the second moment is at most (2+sqrt 2) times
  sum_l sqrt(x_l) * min(1, cap_l, vote_l), x_l = 2^l d^2, where cap_l is the
  error union bound e^{-2x} + e^{-x} plus the wrong-side early stops of both
  classifiers, and vote_l is 1/4 plus both kinds of early stop of the smaller
  one; level 0 has weight 1. The supremum is over d^2 in (0, 1/4].

These are the best constants the method can give with exact sums and the best
split at every level; the certified Lean constants are 26/5 and 13/2.
The level sum of sigma_H stops at x_l > xmax. The error terms at level l
decay like 2^{-(2b - 1/2) l} relative to sqrt(x_l), so the sums converge only
for b > 1/4; for b <= 1/4 the truncated value is not a bound of anything.
Floating point; not a proof.
"""
import math
import numpy as np

R = 2 ** -0.5
L2 = math.log(2)


def vj(j, a, b):
    return a + b * j * L2


def Phi(y, a, b, J=400):
    j = np.arange(1, J + 1)
    v = a + b * j * L2
    sig = np.where(y < v, 1.0, np.exp(-2 * (math.sqrt(y) - np.sqrt(v)) ** 2))
    return float((R ** j * sig).sum())


def kappa_H(a=1.0, b=1.0, grid=400):
    best = 0.0
    for t in range(grid):
        s = 2 ** (t / grid)
        G = sum(math.sqrt(2.0 ** i * s) * Phi(2.0 ** i * s, a, b) for i in range(-60, 24))
        best = max(best, (1 - R) * G)
    return best


def sigma_H(a=1.0, b=1.0, grid=200, depth=60, xmax=400.0):
    """sup over u = d^2 in (0, 1/4] of (2+sqrt2) * sum_l sqrt(x_l) * P_l bound."""
    best = (0.0, None)
    for m in range(2, depth):
        for t in range(grid):
            u = 0.25 * 2.0 ** (-(m - 2) - t / grid)
            tot = 0.0
            for l in range(0, depth + 40):
                x = u * 2 ** l
                if x > xmax:
                    break
                if l == 0:
                    w = 1.0
                else:
                    E_big = sum(math.exp(-2 * (math.sqrt(u * 2 ** k) + math.sqrt(vj(l - k, a, b))) ** 2) for k in range(l))
                    E_small = sum(math.exp(-2 * (math.sqrt(u * 2 ** k) + math.sqrt(vj(l - 1 - k, a, b))) ** 2) for k in range(l - 1))
                    Dsm = 0.0
                    for k in range(l - 1):
                        y = u * 2 ** k; v = vj(l - 1 - k, a, b)
                        Dsm += 1.0 if y >= v else math.exp(-2 * (math.sqrt(v) - math.sqrt(y)) ** 2)
                    cap = math.exp(-2 * x) + math.exp(-x) + E_big + E_small
                    vote = 0.25 + Dsm + E_small
                    w = min(1.0, cap, vote)
                tot += math.sqrt(x) * w
            val = (2 + math.sqrt(2)) * tot
            if val > best[0]:
                best = (val, u)
        if m > 12 and best[1] is not None and best[1] > 0.25 * 2.0 ** (-(m - 4)):
            break
    return best
