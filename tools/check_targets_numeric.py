"""Numerical sanity check that every frozen Lean target is TRUE.

This is not a proof. It guards against wasting agent time on a false or
mistyped statement. Every target in tools/targets.json has a checker here,
and the script fails loudly on any counterexample or any unchecked target.

Run:  python tools/check_targets_numeric.py      (~1-2 minutes)
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import mpmath as mp
import numpy as np

mp.mp.dps = 60
rng = np.random.default_rng(20261026)
ROOT = Path(__file__).resolve().parents[1]
TOL = mp.mpf("1e-40")


def klB(u, v):
    u, v = mp.mpf(u), mp.mpf(v)
    t1 = u * mp.log(u / v) if u != 0 else mp.mpf(0)
    t2 = (1 - u) * mp.log((1 - u) / (1 - v)) if u != 1 else mp.mpf(0)
    return t1 + t2


def rhoPlus(e, L):
    e, L = mp.mpf(e), mp.mpf(L)
    return (mp.mpf(1) / 2 + e) * L / ((mp.mpf(1) / 2 - e) + (mp.mpf(1) / 2 + e) * L)


def rhoMinus(e, L):
    e, L = mp.mpf(e), mp.mpf(L)
    return (mp.mpf(1) / 2 - e) * L / ((mp.mpf(1) / 2 + e) + (mp.mpf(1) / 2 - e) * L)


def pred(d, r):
    return mp.mpf(1) / 2 - mp.mpf(d) + 2 * mp.mpf(d) * r


def etaHard(h, d):
    return mp.mpf(1) / 8 * min(mp.mpf(1), mp.mpf(h) / mp.mpf(d))


def U(a, b, n):
    return [mp.mpf(x) for x in rng.uniform(a, b, n)]


def logU(a, b, n):
    return [mp.mpf(10) ** mp.mpf(x) for x in rng.uniform(a, b, n)]


N = 400
results = {}


def check(name):
    def deco(f):
        worst = f()
        results[name] = worst
        return f
    return deco


def ok(lhs, rhs, slack=TOL):
    """Return margin rhs - lhs (must be >= -slack)."""
    return rhs - lhs


# ---------- Group A ----------
@check("posterior_identity")
def _():
    w = mp.mpf(0)
    for e, L in zip(U(0, 0.4999, N), logU(-8, 8, N)):
        lhs = rhoPlus(e, L) - rhoMinus(e, L)
        rhs = 2 * e * L / (L + (mp.mpf(1) / 4 - e**2) * (L - 1) ** 2)
        w = max(w, abs(lhs - rhs) / (abs(rhs) + mp.mpf("1e-30")))
    assert w < 1e-30, w
    return -w


@check("posterior_diff_le")
def _():
    return min(ok(rhoPlus(e, L) - rhoMinus(e, L), 2 * e) for e, L in zip(U(0, 0.4999, N), logU(-8, 8, N)))


@check("posterior_mem")
def _():
    w = mp.inf
    for e, L in zip(U(0, 0.4999, N), logU(-8, 8, N)):
        rp, rm = rhoPlus(e, L), rhoMinus(e, L)
        w = min(w, rm, rp - rm, 1 - rp)
    return w


@check("pred_variance_ge")
def _():
    w = mp.inf
    for d, r in zip(U(0, 0.5, N), U(-3, 3, N)):
        x = pred(d, r)
        w = min(w, x * (1 - x) - r * (1 - r))
    return w


@check("ratio_bound")
def _():
    w = mp.inf
    for a, b, L in zip(logU(-3, 3, N), logU(-3, 3, N), logU(-6, 6, N)):
        w = min(w, (1 / (4 * a * b) - L / (b + a * L) ** 2) * (4 * a * b))
    return w


# ---------- Group B ----------
@check("kl_taylor_bound")
def _():
    w = mp.inf
    for u, v in zip(U(1e-6, 1 - 1e-6, N), U(1e-6, 1 - 1e-6, N)):
        rhs = (u - v) ** 2 / (2 * min(u * (1 - u), v * (1 - v)))
        w = min(w, rhs - klB(u, v))
    return w


def lemmaA(direction):
    w = mp.inf
    ds = U(1e-4, 0.5, N) + [mp.mpf(1) / 2] * 20
    es = U(0, 0.49, N + 20)
    Ls = logU(-10, 10, N + 20)
    for d, e, L in zip(ds, es, Ls):
        p, m = pred(d, rhoPlus(e, L)), pred(d, rhoMinus(e, L))
        val = klB(p, m) if direction > 0 else klB(m, p)
        rhs = 32 * d**2 * e**2 / (1 - 4 * e**2) ** 2
        w = min(w, (rhs - val) / (rhs + mp.mpf("1e-50")))
    return w


@check("lemmaA_forward")
def _():
    return lemmaA(+1)


@check("lemmaA_reverse")
def _():
    return lemmaA(-1)


@check("lemmaA_sharp_at_one")
def _():
    worst = mp.mpf(0)
    for d in [mp.mpf("0.001"), mp.mpf("0.1"), mp.mpf("0.25"), mp.mpf("0.5")]:
        e = mp.mpf("1e-12")
        r = klB(pred(d, rhoPlus(e, 1)), pred(d, rhoMinus(e, 1))) / (32 * d**2 * e**2 / (1 - 4 * e**2) ** 2)
        worst = max(worst, abs(r - 1))
    assert worst < 1e-15, worst
    return mp.mpf(1e-15) - worst  # margin of the convergence check


@check("hardpair_step_kl")
def _():
    w = mp.inf
    for d, h, L in zip(list(U(1e-4, 0.5, N)) + [mp.mpf(1) / 2] * 20, logU(-4, 1, N + 20), logU(-10, 10, N + 20)):
        e = etaHard(h, d)
        val = klB(pred(d, rhoPlus(e, L)), pred(d, rhoMinus(e, L)))
        rhs = mp.mpf(128) / 225 * h**2
        w = min(w, (rhs - val) / rhs)
    return w


# ---------- Group C ----------
@check("sym_kl_hellinger_pointwise")
def _():
    w = mp.inf
    for x, y in zip(logU(-6, 6, N), logU(-6, 6, N)):
        lhs = 4 * (mp.sqrt(x) - mp.sqrt(y)) ** 2
        rhs = (x - y) * mp.log(x / y)
        w = min(w, rhs - lhs)
    return w


def rand_simplex(n, positive=True):
    v = rng.dirichlet(np.ones(n) * rng.uniform(0.2, 3))
    if not positive and n >= 2 and rng.random() < 0.5:
        v[rng.integers(n)] = 0
        v = v / v.sum()
    v = [mp.mpf(x) for x in v]
    tot = sum(v)
    return [x / tot for x in v]  # renormalize in high precision so sums are exactly 1


def hell2(p, q):
    return 1 - sum(mp.sqrt(a * b) for a, b in zip(p, q))


def klFin(p, q):
    return sum(a * mp.log(a / b) for a, b in zip(p, q))


@check("kl_ge_two_hell_finite")
def _():
    w = mp.inf
    for _ in range(N):
        n = int(rng.integers(1, 9))
        p, q = rand_simplex(n), rand_simplex(n)
        w = min(w, klFin(p, q) - 2 * hell2(p, q))
    return w


@check("sym_kl_ge_eight_hell_finite")
def _():
    w = mp.inf
    for _ in range(N):
        n = int(rng.integers(1, 9))
        p, q = rand_simplex(n), rand_simplex(n)
        w = min(w, klFin(p, q) + klFin(q, p) - 8 * hell2(p, q))
    return w


@check("two_point_variance_finite")
def _():
    w = mp.inf
    for _ in range(N):
        n = int(rng.integers(1, 9))
        p, q = rand_simplex(n, False), rand_simplex(n, False)
        Y = [mp.mpf(x) for x in rng.normal(size=n) * rng.uniform(0.1, 10)]
        mP = sum(a * y for a, y in zip(p, Y))
        mQ = sum(a * y for a, y in zip(q, Y))
        vP = sum(a * (y - mP) ** 2 for a, y in zip(p, Y))
        vQ = sum(a * (y - mQ) ** 2 for a, y in zip(q, Y))
        H = hell2(p, q)
        w = min(w, 4 * H * (vP + vQ) - (mP - mQ) ** 2 * (1 - 2 * H))
    return w


# ---------- Group D ----------
def fg(d, q):
    p = pred(d, q)
    y1 = (1 - mp.mpf(1) / 2 + d) / (2 * d)
    y0 = (0 - mp.mpf(1) / 2 + d) / (2 * d)
    return p, y1, y0


@check("fixed_gap_unbiased")
def _():
    w = mp.mpf(0)
    for d, q in zip(U(1e-4, 0.5, N), U(-2, 3, N)):
        p, y1, y0 = fg(d, q)
        w = max(w, abs(p * y1 + (1 - p) * y0 - q))
    assert w < 1e-40
    return -w


@check("fixed_gap_variance")
def _():
    w = mp.inf
    for d, q in zip(U(1e-4, 0.5, N), U(-2, 3, N)):
        p, y1, y0 = fg(d, q)
        v = p * (y1 - q) ** 2 + (1 - p) * (y0 - q) ** 2
        w = min(w, (1 / (16 * d**2) - v) * d**2)
    return w


@check("fixed_gap_equality")
def _():
    w = mp.mpf(0)
    for d in U(1e-4, 0.5, N):
        p, y1, y0 = fg(d, mp.mpf(1) / 2)
        v = p * (y1 - mp.mpf(1) / 2) ** 2 + (1 - p) * (y0 - mp.mpf(1) / 2) ** 2
        w = max(w, abs(v - 1 / (16 * d**2)) * d**2)
    assert w < 1e-40
    return -w


# ---------- Group E ----------
def series(f, p, kmax=None):
    return mp.nsum(lambda k: f(k, p), [0, mp.inf])


@check("negbin_total")
def _():
    w = mp.mpf(0)
    for p in list(U(0.01, 1, 40)) + [mp.mpf(1)]:
        s = series(lambda k, p: (k + 1) * p**2 * (1 - p) ** k, p)
        w = max(w, abs(s - 1))
    assert w < 1e-30, w
    return -w


@check("negbin_mean")
def _():
    w = mp.mpf(0)
    for p in list(U(0.01, 1, 40)) + [mp.mpf(1)]:
        s = series(lambda k, p: (k + 2) * ((k + 1) * p**2 * (1 - p) ** k), p)
        w = max(w, abs(s - 2 / p) * p)
    assert w < 1e-30, w
    return -w


@check("haldane_inverse_moment")
def _():
    w = mp.mpf(0)
    for p in list(U(0.01, 1, 40)) + [mp.mpf(1)]:
        s = series(lambda k, p: (1 / (k + 1)) * ((k + 1) * p**2 * (1 - p) ** k), p)
        w = max(w, abs(s - p) / p)
    assert w < 1e-30, w
    return -w


# ---------- Group F ----------
@check("scaling_up_pointwise")
def _():
    w = mp.inf
    for c, h, x in zip(U(1, 20, N), logU(-4, 2, N), logU(-4, 1, N)):
        w = min(w, c * min(1, h / x) - min(1, c * h / x))
    return w


@check("scaling_down_pointwise")
def _():
    w = mp.inf
    for b, h, x in zip(U(1e-3, 1, N), logU(-4, 2, N), logU(-4, 1, N)):
        w = min(w, min(1, b * h / x) - b * min(1, h / x))
    return w


@check("modulus_scaling_up")
def _():
    # discrete probability laws on (0, 1]: integral = weighted sum
    w = mp.inf
    for _ in range(N):
        k = int(rng.integers(1, 8))
        xs = logU(-4, 0, k)
        ws = rand_simplex(k)
        c, h = U(1, 20, 1)[0], logU(-4, 1, 1)[0]
        lhs = sum(a * min(1, c * h / x) for a, x in zip(ws, xs))
        rhs = c * sum(a * min(1, h / x) for a, x in zip(ws, xs))
        w = min(w, rhs - lhs)
    return w


@check("power_modulus_critical")
def _():
    w = mp.mpf(0)
    for u in U(0.001, 0.999, 30):
        val = mp.quad(lambda t: min(1, u / t), [0, u, 1])
        w = max(w, abs(val - u * (1 - mp.log(u))))
    assert w < 1e-30, w
    return -w


@check("power_modulus")
def _():
    w = mp.mpf(0)
    for a, u in zip(U(0.05, 4, 40), U(0.001, 0.999, 40)):
        if abs(a - 1) < 1e-3:
            continue
        # [0,u]: substitute t = exp(-y) to remove the endpoint singularity
        left = mp.quad(lambda y: a * mp.e ** (-a * y), [-mp.log(u), mp.inf])
        right = mp.quad(lambda t: (u / t) * a * t ** (a - 1), [u, 1])
        w = max(w, abs(left + right - (a * u - u**a) / (a - 1)))
    assert w < 1e-30, w
    return -w


# ---------- Group G ----------
r = 1 / mp.sqrt(2)


@check("constant_second_moment")
def _():
    return 85 - 5 / (1 - r) * (1 / (1 - r) + 1 / (1 - r**3))


@check("constant_work")
def _():
    return 149 - 34 * (2 + mp.log(2) + r * mp.log(2) / (1 - r))


@check("kl_delta_identity")
def _():
    w = mp.mpf(0)
    for dl in U(1e-6, 0.4999, N):
        w = max(w, abs(klB(1 - dl, dl) - (1 - 2 * dl) * mp.log((1 - dl) / dl)))
    assert w < 1e-40
    return -w


@check("kl_delta_lower")
def _():
    w = mp.inf
    for dl in list(logU(-12, math.log10(0.25), N)) + [mp.mpf(1) / 4]:
        w = min(w, (1 - 2 * dl) * mp.log((1 - dl) / dl) - mp.log(1 / dl) / 4)
    return w


# ---------- Group H ----------
@check("error_tail_bound")
def _():
    w = mp.inf
    for x in list(logU(0, 4, N)) + [mp.mpf(1)]:
        w = min(w, (x ** -2 - mp.e ** (-2 * x) - mp.e ** -2 * mp.mpf(2) / 3 * x ** -2) * x**2)
    return w


@check("classifier_scale_step")
def _():
    w = mp.inf
    cnt = 0
    while cnt < N:
        Nn = mp.mpf(2) ** int(rng.integers(0, 20))
        n = Nn * mp.mpf(rng.uniform(1e-6, 1))
        d = logU(-4, math.log10(0.5), 1)[0]
        if Nn * d**2 < 1:
            continue
        if not d <= 2 * mp.sqrt((1 + mp.log(Nn / n)) / n):
            continue
        cnt += 1
        w = min(w, 4 * (1 + mp.log(Nn * d**2)) - n * d**2)
    return w


def dyadic(v, b):
    return mp.nsum(lambda k: (mp.mpf(2) ** k) ** v * mp.e ** (-(b * mp.mpf(2) ** k)), [0, mp.inf])


@check("dyadic_sum_v1")
def _():
    return min((2 / b - dyadic(1, b)) * b for b in logU(-4, 3, 60))


@check("dyadic_sum_v2")
def _():
    return min((mp.mpf(8) / (3 * b**2) - dyadic(2, b)) * b**2 for b in logU(-4, 3, 60))


# ---------- report ----------
targets = json.loads((ROOT / "tools" / "targets.json").read_text())["targets"]
names = [t["name"] for t in targets]
missing = [n for n in names if n not in results]
bad = {n: v for n, v in results.items() if v < -mp.mpf("1e-25") and n in names}
print(f"{'target':32s} min margin (>= 0 means true on all samples)")
for n in names:
    if n in results:
        print(f"{n:32s} {mp.nstr(results[n], 6)}")
if missing:
    print("UNCHECKED TARGETS:", missing)
if bad:
    print("COUNTEREXAMPLES:", list(bad))
if missing or bad:
    sys.exit(1)
print(f"\nAll {len(names)} targets numerically consistent.")
