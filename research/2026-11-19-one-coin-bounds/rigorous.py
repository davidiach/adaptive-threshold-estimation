"""The Lean proof's method at a fixed gap, with a rigorous sharp tail bound.

tails.py evaluates the method in the large-n limit, with tail proxies. Here
every event is the exact binomial event at its check: n = 2^k flips of a coin
with p = 1/2 + d, and the integer success counts that the strict threshold
comparisons of the classifier select. Each probability is bounded by the
smaller of

* Hoeffding: exp(-2 n eps^2), eps the distance of the cut from p;
* Bahadur's bound: P(X >= k) <= P(X = k) / (1 - rho), with
  rho = (n-k) p / ((k+1) q) < 1, the geometric series of the term ratios.
  It is elementary; a proof would also need an upper bound for the
  binomial term, for which Robbins' form of Stirling's formula loses at
  most a factor exp(1/(12 n)). Setting USE_BAHADUR = False leaves Hoeffding
  alone, which checks this code against the limits of tails.py.

With central=True, a probability whose cut lies on the far side of the
mean is also bounded through the median: a binomial median lies in
[floor(np), ceil(np)], so P(X <= m) <= 1/2 + (m - floor(np) + 1) * P_max for
m >= floor(np), with P_max the largest binomial term, and symmetrically for
upper tails. The median fact is a known theorem (Kaas and Buhrman, 1980);
it is not in Mathlib.

The structure of the bounds is that of tails.py. Only the positive sign is
computed. Floating point; not a proof.
"""
import math
import numpy as np
from scipy.stats import binom

R = 2 ** -0.5
USE_BAHADUR = True


def upper(n, k, p, central=False):
    """Bound for P(X >= k), X ~ Bin(n, p); k may be an array."""
    k = np.asarray(k, dtype=float)
    q = 1 - p
    out = np.ones_like(k)
    hi = k > n
    out[hi] = 0.0
    mid = (k > 0) & ~hi
    kk = k[mid]
    eps = kk / n - p
    hoeff = np.where(eps > 0, np.exp(-2 * n * np.maximum(eps, 0) ** 2), 1.0)
    with np.errstate(divide='ignore', invalid='ignore'):
        rho = (n - kk) * p / ((kk + 1) * q)
        bah = np.where(rho < 1, np.exp(binom.logpmf(kk, n, p)) / (1 - rho), 1.0)
    if not USE_BAHADUR:
        bah = np.ones_like(kk)
    best = np.minimum(1.0, np.minimum(hoeff, bah))
    if central:
        top = math.ceil(n * p)
        pmax = float(np.exp(binom.logpmf(math.floor((n + 1) * p), n, p)))
        cen = np.where(kk <= top, 0.5 + (top - kk + 1) * pmax, 0.5)
        best = np.minimum(best, cen)
    out[mid] = best
    return out


def lower(n, m, p, central=False):
    """Bound for P(X <= m), X ~ Bin(n, p)."""
    return upper(n, n - np.asarray(m, dtype=float), 1 - p, central)


def thr(n, M, a, b):
    return np.sqrt((a + b * np.log(M / n)) / n)


def sigma_levels(d, a=1.0, b=1.0, xmax=4000.0, central=False):
    """x_l and the weights w_l of the second-moment bound at gap d."""
    p = 0.5 + d
    xs, ws = [d * d], [1.0]                  # level 0, weight 1
    l = 1
    while d * d * 2 ** l <= xmax:
        M = 2 ** l
        c = central
        cap = lower(M, [M // 2], p, c)[0] + lower(M // 2, [(M // 2) // 2], p, c)[0]
        n = 2.0 ** np.arange(l)                       # checks of the big classifier
        tb = thr(n, M, a, b)
        e_big = sum(lower(int(nn), [math.ceil(nn * (0.5 - t)) - 1], p, c)[0] for nn, t in zip(n, tb))
        ns = 2.0 ** np.arange(l - 1)                  # checks of the small classifier before its cap
        ts = thr(ns, M / 2, a, b)
        e_small = sum(lower(int(nn), [math.ceil(nn * (0.5 - t)) - 1], p, c)[0] for nn, t in zip(ns, ts))
        d_small = sum(upper(int(nn), [math.floor(nn * (0.5 + t)) + 1], p, c)[0] for nn, t in zip(ns, ts))
        xs.append(d * d * M)
        ws.append(min(1.0, cap + e_big + e_small, 0.25 + d_small + e_small))
        l += 1
    return np.array(xs), np.array(ws)


def sigma_at(d, a=1.0, b=1.0, central=False):
    """(2 + sqrt 2) * sum_l sqrt(x_l) * w_l at gap d, positive coin."""
    x, w = sigma_levels(d, a, b, central=central)
    return (2 + math.sqrt(2)) * float((np.sqrt(x) * w).sum())


def kappa_at(d, a=1.0, b=1.0, extra=50, central=False):
    """d * (1 + sum_l p_l sum_{k<l} 2^k surv(l, k)) at gap d, positive coin,
    with surv(l, k) <= P(S_n <= n (1/2 + t)) at the check n = 2^k."""
    p = 0.5 + d
    lmax = math.ceil(math.log2(1 / (d * d))) + extra
    tot = 1.0
    cache = {}
    for l in range(1, lmax + 1):
        pl = (1 - R) * R ** l
        s = 0.0
        for k in range(l):
            n = 2 ** k
            key = (k, l - k)
            if key not in cache:
                t = math.sqrt((a + b * math.log(2 ** (l - k))) / n)
                m = math.floor(n * (0.5 + t))
                if n > 2 ** 40:
                    eps = p - m / n
                    cache[key] = math.exp(-2 * n * eps * eps) if eps > 0 else 1.0
                else:
                    cache[key] = lower(n, [m], p, central)[0]
            s += n * cache[key]
        tot += pl * s
    return d * tot
