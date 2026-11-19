"""Exact one-call quantities of the distribution-blind estimator, generalized.

Copied from ../2026-11-18-upper-constant/blind.py and extended in two ways:

* the classifier threshold is sqrt((a + b*log(cap/n))/n); the estimator of the
  paper and of Lean has a = b = 1;
* the calibration denominator may be lam*N with lam >= 1 (the batch at scale
  lam*N of Appendix AB), so the mean-square error is
  bias^2 + Var(V) * c / (lam*N).

Everything is floating point. Nothing here is a proof.
"""
import math, functools
import numpy as np
from scipy.signal import fftconvolve
from scipy.stats import binom

R = 2 ** -0.5


def p_level(l):
    return (1 - R) * R ** l


def thr(n, cap, a=1.0, b=1.0):
    return math.sqrt((a + b * math.log(cap / n)) / n)


def conv(x, pmf):
    if len(x) * len(pmf) < 4096:
        y = np.convolve(x, pmf)
    else:
        y = fftconvolve(x, pmf)
    y[y < 0] = 0.0
    return y


@functools.lru_cache(maxsize=None)
def level_stats(p, l, a=1.0, b=1.0):
    """For one coin with success probability p and the coupled call at level l:
    (P(Z_l = 1), P(Z_l != Z_{l-1}), E[flips])."""
    N = 2 ** l
    Nc = N // 2
    und = np.array([1.0]) if l > 0 else np.array([0.0])
    c0 = np.array([0.0]) if l > 0 else np.array([1.0])  # level 0: Z_{-1} = 0
    c1 = np.array([0.0])
    n = 0
    za = D = En = 0.0
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
            cstop = (n >= Nc) | (dev > thr(n, Nc, a, b))
            c1 = c1 + und * (cstop & lab1)
            c0 = c0 + und * (cstop & ~lab1)
            und = und * (~cstop)
        fstop = (n >= N) | (dev > thr(n, N, a, b))
        assert und[fstop].sum() < 1e-12
        tot = c0 + c1
        En += n * tot[fstop].sum()
        za += tot[fstop & lab1].sum()
        D += c0[fstop & lab1].sum() + c1[fstop & ~lab1].sum()
        c0 = c0 * (~fstop); c1 = c1 * (~fstop); und = und * (~fstop)
        if n >= N:
            break
        if (c0.sum() + c1.sum() + und.sum()) < 1e-17:
            break
    return za, D, En


def sign_parts(d, L, a=1.0, b=1.0):
    """Per sign s = +1, -1: (P(Z_L = 1), E V^2, mean padded cost) at cutoff L."""
    pl = np.array([p_level(l) for l in range(L + 1)])
    out = {}
    for s, p in ((1, 0.5 + d), (-1, 0.5 - d)):
        st = np.array([level_stats(p, l, a, b) for l in range(L + 1)])
        out[s] = (st[L, 0], (st[:, 1] / pl).sum(), (pl * st[:, 2]).sum() + R ** (L + 1))
    return out


def mse_parts(parts, L, lam=1.0):
    """parts: list of (sign_parts, weight, q). Returns (MSE, bias, Var V, c)."""
    N = 2 ** L
    u = th = S = c = 0.0
    for st, w, q in parts:
        for s, ws in ((1, q), (-1, 1 - q)):
            A, Sp, cp = st[s]
            u += w * ws * A; S += w * ws * Sp; c += w * ws * cp
        th += w * q
    var = S - u * u
    return (u - th) ** 2 + var * c / (lam * N), u - th, var, c


def omega(atoms, h):
    return sum(w * min(1.0, h / d) for d, w, q in atoms)
