"""The call constants of the Lean proof's method, with a choice of tail bound.

The Lean proof bounds the padded call cost and the call second moment by
union bounds over the classifiers' checks and levels, with one Gaussian-scale
tail estimate per event. Each event is a deviation of the success fraction
of n flips: written in units of the standard deviation 1/(2 sqrt n), an
event "at least w" gets the bound T(w). The proof uses Hoeffding,
T(w) = exp(-w^2/2). This module evaluates the same bounds with

* 'hoeffding': exp(-w^2/2), the bound Lean uses;
* 'mills': min(exp(-w^2/2), phi(w)/w), the Mills-ratio bound that a sharp
  binomial tail inequality would give for large n;
* 'sharp': 'mills' capped at 1/2 for w > 0, and 1/2 + |w|/sqrt(2 pi), the
  tangent of the normal distribution function at 0, for w <= 0. Both are
  upper bounds for the Gaussian probability; for the binomial they hold up to
  lattice corrections of order n^{-1/2};
* 'gauss': the Gaussian tail itself, 1 - Phi(w). This is the large-n limit
  of each single probability, not a bound valid for every n.

With T = 'hoeffding' the functions reproduce kappa_H and sigma_H of
../2026-11-19-upper-constant-12/hoeffding.py; see that module for the
structure of the bounds. Thresholds sqrt((a + b log(cap/n))/n), with
v_j = a + b j log 2. Floating point; not a proof.
"""
import math
import numpy as np
from scipy.special import ndtr

R = 2 ** -0.5
L2 = math.log(2)


def tail(w, kind):
    w = np.asarray(w, dtype=float)
    if kind == 'hoeffding':
        return np.where(w <= 0, 1.0, np.exp(-np.maximum(w, 0) ** 2 / 2))
    if kind == 'mills':
        with np.errstate(divide='ignore', invalid='ignore'):
            m = np.exp(-w ** 2 / 2) / (np.sqrt(2 * np.pi) * w)
        h = np.exp(-np.maximum(w, 0) ** 2 / 2)
        return np.where(w <= 0, 1.0, np.minimum(h, np.where(w > 0, m, 1.0)))
    if kind == 'sharp':
        # Mills for w > 0 (and at most 1/2), the tangent of Phi at 0 for w <= 0
        with np.errstate(divide='ignore', invalid='ignore'):
            m = np.exp(-w ** 2 / 2) / (np.sqrt(2 * np.pi) * w)
        pos = np.minimum(0.5, np.minimum(np.exp(-np.maximum(w, 0) ** 2 / 2), np.where(w > 0, m, 1.0)))
        neg = np.minimum(1.0, 0.5 - np.minimum(w, 0) / np.sqrt(2 * np.pi))
        return np.where(w > 0, pos, neg)
    if kind == 'gauss':
        return ndtr(-w)
    raise ValueError(kind)


def vj(j, a, b):
    return a + b * np.asarray(j, dtype=float) * L2


def Phi(y, kind, a=1.0, b=1.0, J=400):
    """sum_{j>=1} r^j * T(2(sqrt y - sqrt v_j)): survival bound at one check."""
    j = np.arange(1, J + 1)
    return float((R ** j * tail(2 * (math.sqrt(y) - np.sqrt(vj(j, a, b))), kind)).sum())


def kappa_curve(kind, a=1.0, b=1.0, grid=200):
    """(1-r) * sum_i sqrt(2^i s) Phi(2^i s) for s = 2^(t/grid), t < grid."""
    out = []
    for t in range(grid):
        s = 2 ** (t / grid)
        out.append((1 - R) * sum(math.sqrt(2.0 ** i * s) * Phi(2.0 ** i * s, kind, a, b)
                                 for i in range(-60, 24)))
    return np.array(out)


def sigma_levels(u, kind, a=1.0, b=1.0, xmax=4000.0):
    """Per-level weights w_l and x_l of the second-moment bound at d^2 = u.

    d * E V^2 <= (2 + sqrt 2) * sum_l sqrt(x_l) * w_l, with w_0 = 1 and
    w_l = min(1, cap_l, vote_l) as in hoeffding.sigma_H."""
    xs, ws = [u], [1.0]
    l = 1
    while u * 2 ** l <= xmax:
        x = u * 2 ** l
        k = np.arange(l)
        yk = u * 2.0 ** k
        e_big = tail(2 * (np.sqrt(yk) + np.sqrt(vj(l - k, a, b))), kind).sum()
        k2 = np.arange(l - 1)
        yk2 = u * 2.0 ** k2
        e_small = tail(2 * (np.sqrt(yk2) + np.sqrt(vj(l - 1 - k2, a, b))), kind).sum()
        d_small = tail(2 * (np.sqrt(vj(l - 1 - k2, a, b)) - np.sqrt(yk2)), kind).sum()
        cap = float(tail(2 * math.sqrt(x), kind) + tail(math.sqrt(2 * x), kind)) + e_big + e_small
        vote = 0.25 + d_small + e_small
        xs.append(x); ws.append(min(1.0, cap, vote))
        l += 1
    return np.array(xs), np.array(ws)


def sigma_at(u, kind, a=1.0, b=1.0):
    x, w = sigma_levels(u, kind, a, b)
    return (2 + math.sqrt(2)) * float((np.sqrt(x) * w).sum())


def sigma_curve(kind, a=1.0, b=1.0, octaves=40, per=24):
    """sigma bound at u = d^2 = 2^(-2 - t/per), t < octaves*per; returns (u, values)."""
    us = 0.25 * 2.0 ** (-np.arange(octaves * per) / per)
    return us, np.array([sigma_at(u, kind, a, b) for u in us])
