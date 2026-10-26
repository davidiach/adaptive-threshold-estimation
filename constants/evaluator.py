"""Exact (non-Monte-Carlo) evaluator for the capped-classifier MLMC estimator.

FROZEN. Agents tune parameters in constants/candidate.json, not this file.

Model (v4 Section 4): a coin with P = 1/2 + (2S-1)d. A classifier with dyadic cap N
inspects prefixes n = 1, 2, 4, ..., N and stops early at n < N when
    |mean_n - 1/2| > t(n, N),   t(n, N) = sqrt((k1 + k2 * log(N/n)) / n);
otherwise it outputs 1{mean_N > 1/2} (a tie is negative). Level differences
Delta_l = Z_{2^l} - Z_{2^{l-1}} share one coin stream; the single-term estimator
uses P(J = l) = (1 - r) r^l with r = 2^{-1/2}. v4 uses k1 = k2 = 1.

For each (d, S) the evaluator computes exactly, via a probability recursion over
shared success counts and both stopping states:
    e_N           misclassification probability of the cap-N classifier;
    E[Delta_l^2]  and E[max(tau_{2^l}, tau_{2^{l-1}})]  for each level.
"""
from __future__ import annotations

import math
from functools import lru_cache

import numpy as np
from scipy.signal import fftconvolve
from scipy.stats import binom

R = 2 ** -0.5


def _thr(n: int, N: int, k1: float, k2: float) -> float:
    return math.sqrt((k1 + k2 * math.log(N / n)) / n)


def _decide(xbar, n, cap, k1, k2):
    if n < cap:
        t = _thr(n, cap, k1, k2)
        pos = (xbar - 0.5) > t
        neg = (0.5 - xbar) > t
        return pos, neg, ~(pos | neg)
    pos = xbar > 0.5
    return pos, ~pos, np.zeros_like(pos)


def coupled(caps: tuple[int, ...], d: float, S: int, k1: float, k2: float) -> dict:
    """Joint exact law of classifiers with the given caps on one coin stream."""
    p = 0.5 + (2 * S - 1) * d
    K = len(caps)
    live = {tuple([0] * K): np.array([1.0])}
    term: dict[tuple, float] = {}
    emax = 0.0
    n_prev, n = 0, 1
    while n <= max(caps) and live:
        pmf = binom.pmf(np.arange(n - n_prev + 1), n - n_prev, p)
        xbar = np.arange(n + 1) / n
        nxt: dict[tuple, np.ndarray] = {}
        for st, arr in live.items():
            a0 = np.clip(fftconvolve(arr, pmf), 0, None)[: n + 1]
            parts = [(st, a0)]
            for i, c in enumerate(caps):
                if st[i] != 0 or n > c:
                    continue
                pos, neg, run_ = _decide(xbar, n, c, k1, k2)
                new = []
                for s, a in parts:
                    for flag, m in ((1, pos), (2, neg), (0, run_)):
                        if m.any():
                            s2 = list(s)
                            s2[i] = flag
                            new.append((tuple(s2), np.where(m, a, 0.0)))
                parts = new
            for s, a in parts:
                if 0 in s:
                    nxt[s] = nxt.get(s, 0) + a
                else:
                    mass = float(a.sum())
                    term[s] = term.get(s, 0.0) + mass
                    emax += n * mass
        live = nxt
        n_prev, n = n, 2 * n
    out = {"total": sum(term.values()), "emax": emax}
    for i in range(K):
        out[f"p1_{i}"] = sum(m for s, m in term.items() if s[i] == 1)
    if K == 2:
        out["pdiff"] = sum(m for s, m in term.items() if s[0] != s[1])
    return out


@lru_cache(maxsize=None)
def profile(d: float, S: int, Lmax: int, k1: float, k2: float) -> dict:
    """Per-level exact quantities for one (d, S)."""
    err, e2, ew, mean = [], [], [], []
    for L in range(Lmax + 1):
        r1 = coupled((2 ** L,), d, S, k1, k2)
        err.append((1 - r1["p1_0"]) if S == 1 else r1["p1_0"])
        if L == 0:
            e2.append(r1["p1_0"])       # Delta_0 = Z_1
            ew.append(1.0)
            mean.append(r1["p1_0"])
        else:
            r2 = coupled((2 ** L, 2 ** (L - 1)), d, S, k1, k2)
            e2.append(r2["pdiff"])
            ew.append(r2["emax"])
            mean.append(r2["p1_0"] - r2["p1_1"])
    return {"err": err, "e2": e2, "ew": ew, "mean": mean}


def metrics(ds, Lmax: int, k1: float, k2: float) -> dict:
    """Worst-case ratios over a grid of magnitudes and both signs."""
    pl = [(1 - R) * R ** l for l in range(Lmax + 1)]
    out = {"bias_ratio": 0.0, "c1_all_L": 0.0, "c2_all_L": 0.0,
           "c1_top": 0.0, "c2_top": 0.0, "tele_resid": 0.0}
    for d in ds:
        for S in (0, 1):
            pr = profile(float(d), S, Lmax, k1, k2)
            for L in range(Lmax + 1):
                N = 2 ** L
                scale = min(math.sqrt(N), 1 / d)
                bound = min(1.0, (N * d * d) ** -2)
                out["bias_ratio"] = max(out["bias_ratio"], pr["err"][L] / bound)
                y2 = sum(pr["e2"][l] / pl[l] for l in range(L + 1))
                w = sum(pl[l] * pr["ew"][l] for l in range(L + 1))
                out["c1_all_L"] = max(out["c1_all_L"], y2 / scale)
                out["c2_all_L"] = max(out["c2_all_L"], w / scale)
                if L == Lmax:
                    out["c1_top"] = max(out["c1_top"], y2 * d)
                    out["c2_top"] = max(out["c2_top"], w * d)
                pz1 = (1 - pr["err"][L]) if S == 1 else pr["err"][L]
                out["tele_resid"] = max(out["tele_resid"], abs(sum(pr["mean"][: L + 1]) - pz1))
    out["product_unbiased"] = out["c1_top"] * out["c2_top"]   # proxy for sup VW / I^2
    out["product_finite"] = out["c1_all_L"] * out["c2_all_L"]   # finite-budget constant proxy
    return out
