"""Exact risk of the distribution-blind algorithm (toolkit estimator.py / BlindUpper)."""
import math, functools
import numpy as np
from scipy.signal import fftconvolve
from scipy.stats import binom

R = 2 ** -0.5

def p_level(l):
    return (1 - R) * R ** l

def thr(n, cap):
    return math.sqrt((1 + math.log(cap / n)) / n)

def conv(x, pmf):
    if len(x) * len(pmf) < 4096:
        y = np.convolve(x, pmf)
    else:
        y = fftconvolve(x, pmf)
    y[y < 0] = 0.0
    return y

@functools.lru_cache(maxsize=None)
def level_stats(p, l):
    """For one coin with success probability p and the coupled call at level l:
    returns (P(Z_l = 1), P(Z_l != Z_{l-1}), E[flips])."""
    N = 2 ** l
    Nc = N // 2
    und = np.array([1.0]) if l > 0 else np.array([0.0])
    c0 = np.array([0.0]) if l > 0 else np.array([1.0])  # level 0: Z_{-1} = 0
    c1 = np.array([0.0])
    n = 0
    a = D = En = 0.0
    while True:
        block = 1 if n == 0 else n
        pmf = binom.pmf(np.arange(block + 1), block, p)
        und, c0, c1 = conv(und, pmf), conv(c0, pmf), conv(c1, pmf)
        n += block
        k = np.arange(n + 1)
        mean = k / n
        dev = np.abs(mean - 0.5)
        lab1 = mean > 0.5
        if l > 0:
            cstop = (n >= Nc) | (dev > thr(n, Nc))
            c1 = c1 + und * (cstop & lab1)
            c0 = c0 + und * (cstop & ~lab1)
            und = und * (~cstop)
        fstop = (n >= N) | (dev > thr(n, N))
        assert und[fstop].sum() < 1e-12
        tot = c0 + c1
        En += n * tot[fstop].sum()
        a += tot[fstop & lab1].sum()
        D += c0[fstop & lab1].sum() + c1[fstop & ~lab1].sum()
        c0 = c0 * (~fstop); c1 = c1 * (~fstop); und = und * (~fstop)
        if n >= N:
            break
        if (c0.sum() + c1.sum() + und.sum()) < 1e-17:
            break
    return a, D, En

def coin_stats(d, L):
    """Per-sign arrays over levels 0..L for a coin of gap d."""
    out = {}
    for s, p in ((1, 0.5 + d), (-1, 0.5 - d)):
        st = [level_stats(p, l) for l in range(L + 1)]
        out[s] = np.array(st)  # columns a, D, En
    return out

def mse(atoms, L):
    """atoms: list of (d, w, q). Exact MSE of the raw output at budget level L."""
    N = 2 ** L
    pl = np.array([p_level(l) for l in range(L + 1)])
    u = theta = S = c = 0.0
    for d, w, q in atoms:
        cs = coin_stats(d, L)
        for s, ws in ((1, q), (-1, 1 - q)):
            arr = cs[s]
            u += w * ws * arr[L, 0]
            S += w * ws * (arr[:, 1] / pl).sum()
            c += w * ws * (pl * arr[:, 2]).sum()
        theta += w * q
    c += R ** (L + 1)
    return (u - theta) ** 2 + (S - u * u) * c / N, (u - theta), S - u * u, c / N

def omega(atoms, h):
    return sum(w * min(1.0, h / d) for d, w, q in atoms)
