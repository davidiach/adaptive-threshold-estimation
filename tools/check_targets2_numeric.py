"""Numerical sanity checks for every Tier 2 Lean target.

Not a proof. Each checker implements the Lean definitions in
`lean/ThresholdHC/Statements2.lean` literally (brute force at small sizes) and,
for the classifier targets, cross-checks against the exact recursion in
`constants/evaluator.py` at larger sizes.

Run:  python tools/check_targets2_numeric.py
"""
from __future__ import annotations

import itertools
import json
import math
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "constants"))
from evaluator import coupled, profile  # noqa: E402

rng = np.random.default_rng(271026)
R = 2 ** -0.5
results: dict[str, float] = {}
counts: dict[str, int] = {}


def record(name, margin):
    margin = float(margin)
    if not math.isfinite(margin):
        raise ValueError(f"Non-finite margin for {name}: {margin}")
    results[name] = min(results.get(name, math.inf), margin)
    counts[name] = counts.get(name, 0) + 1


def lean_log(x):
    return 0.0 if x == 0 else math.log(abs(x))  # Mathlib: log 0 = 0, log |x| for x < 0


def klB(u, v):
    a = 0.0 if u == 0 else u * lean_log(u / v if v != 0 else 0.0)
    b = 0.0 if u == 1 else (1 - u) * lean_log((1 - u) / (1 - v) if v != 1 else 0.0)
    return a + b


def klFT(P, Q):
    tot = 0.0
    for p, q in zip(P, Q):
        if p == 0:
            continue
        assert q > 0, "absolute continuity violated in a check"
        tot += p * math.log(p / q)
    return tot


def simplex(n, zeros=False):
    v = rng.dirichlet(np.ones(n) * rng.uniform(0.3, 3))
    if zeros and n > 2:
        k = rng.integers(0, n - 1)
        v[rng.choice(n, size=k, replace=False)] = 0
        v = v / v.sum()
    return v


# ---------------- Group I ----------------
for _ in range(3000):
    n = int(rng.integers(1, 9))
    P = simplex(n, zeros=True)
    Q = simplex(n)
    Q = np.where(P > 0, Q, Q * rng.integers(0, 2, n))  # allow Q = 0 only where P = 0
    if Q.sum() == 0:
        continue
    Q = Q / Q.sum()
    A = rng.random(n) < 0.5
    record("kl_data_processing_finite", klFT(P, Q) - klB(P[A].sum(), Q[A].sum()) + 1e-12)
    Pp, Qp = simplex(n), simplex(n)
    tv = 0.5 * np.abs(Pp - Qp).sum()
    record("pinsker_finite", math.sqrt(max(klFT(Pp, Qp), 0) / 2) - tv + 1e-12)
    th = rng.normal(size=n) * rng.uniform(0.1, 5)
    a, b = sorted(rng.normal(size=2) * 2)
    R2 = max((P * (th - a) ** 2).sum(), (Q * (th - b) ** 2).sum())
    tvPQ = 0.5 * np.abs(P - Q).sum()
    record("two_point_rms_lower", 8 * R2 - (b - a) ** 2 * (1 - tvPQ) + 1e-9)

for kappa in [0.01, 0.3, 0.6, 0.9, 0.999]:
    xs = np.linspace(1 - kappa, 1 + kappa, 20001)
    xs = xs[np.abs(xs - 1) > 1e-6]
    ratio = (-np.log(xs) + xs - 1) / (np.sqrt(xs) - 1) ** 2
    record("bounded_ratio_log", 1.0 if np.isfinite(ratio).all() and ratio.max() < 1e6 else -1.0)


def hist_before(omega, t):
    return tuple(o for o in omega[:t] if o is not None)


def path_prob(pol, p, omega):
    pr = 1.0
    for t in range(len(omega)):
        a = pol.get(hist_before(omega, t))
        o = omega[t]
        if a is None and o is None:
            f = 1.0
        elif a is not None and o is True:
            f = p[a]
        elif a is not None and o is False:
            f = 1 - p[a]
        else:
            f = 0.0
        pr *= f
        if pr == 0:
            break
    return pr


def transcript_law(pol, d, q, n):
    m = len(d)
    omegas = list(itertools.product([None, True, False], repeat=n))
    law = []
    for om in omegas:
        tot = 0.0
        for s in itertools.product([True, False], repeat=m):
            prior = np.prod([q[i] if s[i] else 1 - q[i] for i in range(m)]) if m else 1.0
            p = [0.5 + (d[i] if s[i] else -d[i]) for i in range(m)]
            tot += prior * path_prob(pol, p, om)
        law.append(tot)
    return omegas, np.array(law)


def random_policy(m, n):
    pol = {}
    for k in range(n):
        for h in itertools.product([True, False], repeat=k):
            r = rng.random()
            pol[h] = None if (m == 0 or r < 0.15) else int(rng.integers(0, m))
    return pol


for trial in range(250):
    m, n = int(rng.integers(0, 4)), int(rng.integers(1, 6))
    pol = random_policy(m, n)
    d = rng.uniform(0.01, 0.5, m)
    if m and rng.random() < 0.2:
        d[rng.integers(m)] = 0.5
    q = rng.uniform(0, 1, m)
    om, law = transcript_law(pol, d, q, n)
    record("transcript_law_total", min(1e-12 - abs(law.sum() - 1), law.min() + 1e-15))
    h = float(rng.uniform(0.01, 1.0))
    # half the trials sit exactly on the constraint boundary (eta = min(1/8, h/(8d)))
    scale = np.ones(m) if rng.random() < 0.5 else rng.uniform(0, 1, m)
    eta = np.minimum(1 / 8, h / (8 * d)) * scale if m else np.array([])
    _, Pp = transcript_law(pol, d, 0.5 + eta, n)
    _, Pm = transcript_law(pol, d, 0.5 - eta, n)
    work = np.array([sum(o is not None for o in w) for w in om])
    bound = 128 / 225 * h**2 * float((Pp * work).sum())
    kl = klFT(Pp, Pm)
    record("stopped_transcript_kl", bound - kl + 1e-12)
    A = rng.random(len(om)) < 0.5
    delta = max(1 - Pp[A].sum(), Pm[A].sum())
    if 0 < delta < 0.5:
        record("stopped_transcript_testing", bound - klB(1 - delta, delta) + 1e-12)

# A deterministic, non-vacuous I6 case: one observation reveals the sign.
# d = h = 1/2, eta = 1/8, A = {heads}, and both errors are delta = 3/8.
om, Pp = transcript_law({(): 0}, [0.5], [0.625], 1)
_, Pm = transcript_law({(): 0}, [0.5], [0.375], 1)
A = np.array([w == (True,) for w in om])
delta = 3 / 8
assert 1 - delta <= Pp[A].sum() and Pm[A].sum() <= delta
work = np.array([sum(o is not None for o in w) for w in om])
bound = 128 / 225 * 0.5**2 * float((Pp * work).sum())
record("stopped_transcript_testing", bound - klB(1 - delta, delta) + 1e-12)


# ---------------- Group K / M: literal classifier vs exact recursion ----------------
def thrK(k1, k2, n, N):
    v = (k1 + k2 * math.log(N / n)) / n
    return math.sqrt(v) if v > 0 else 0.0


def classifyK(k1, k2, L, x):
    cs = np.concatenate([[0], np.cumsum(x)])
    for j in range(L + 1):
        n = 2**j
        mean = cs[n] / n
        if j < L:
            t = thrK(k1, k2, n, 2**L)
            if mean - 0.5 > t:
                return True, n
            if 0.5 - mean > t:
                return False, n
        else:
            return (mean > 0.5), n
    return False, 2**L


def brute(k1, k2, L, d, S):
    p = 0.5 + (d if S else -d)
    err = work = 0.0
    e2 = np.zeros(L + 1)
    ew = np.zeros(L + 1)
    mean_delta = np.zeros(L + 1)
    for bits in itertools.product([0, 1], repeat=2**L):
        x = np.array(bits)
        w = p ** x.sum() * (1 - p) ** (len(x) - x.sum())
        outs = [classifyK(k1, k2, l, x) for l in range(L + 1)]
        z = [1.0 if o[0] else 0.0 for o in outs]
        err += w * (outs[L][0] != S)
        work += w * outs[L][1]
        for l in range(L + 1):
            dl = z[0] if l == 0 else z[l] - z[l - 1]
            e2[l] += w * dl * dl
            mean_delta[l] += w * dl
            ew[l] += w * (outs[0][1] if l == 0 else max(outs[l][1], outs[l - 1][1]))
    return err, work, e2, ew, mean_delta, z


def moments(e2, ew, L):
    pl = [(1 - R) * R**l for l in range(L + 1)]
    return sum(e2[l] / pl[l] for l in range(L + 1)), sum(pl[l] * ew[l] for l in range(L + 1))


def mN(N, d):
    return min(N, d**-2 * (1 + max(0.0, math.log(N * d * d))))


# brute force at small L, cross-checked against the exact recursion
for (k1, k2) in [(1.0, 1.0), (0.25, 1.0)]:
    for L in range(0, 4):
        for d in [0.02, 0.1, 0.3, 0.5]:
            for S in (False, True):
                err, work, e2, ew, md, _ = brute(k1, k2, L, d, S)
                pr = profile(float(d), int(S), L, k1, k2)
                assert abs(err - pr["err"][L]) < 1e-12, ("err mismatch", k1, k2, L, d, S)
                assert np.allclose(e2, pr["e2"][: L + 1], atol=1e-12), ("e2 mismatch", L, d)
                assert np.allclose(ew, pr["ew"][: L + 1], atol=1e-12), ("ew mismatch", L, d)
                pz = (1 - err) if S else err
                record("lemma7_telescoping", 1e-12 - abs(md.sum() - pz))
for _ in range(20):  # telescoping holds for arbitrary thresholds
    k1, k2, L = float(rng.uniform(-1, 3)), float(rng.uniform(-1, 3)), int(rng.integers(0, 4))
    d, S = float(rng.uniform(0.01, 0.5)), bool(rng.integers(2))
    err, work, e2, ew, md, _ = brute(k1, k2, L, d, S)
    p = 0.5 + (d if S else -d)
    pz = sum(p ** sum(b) * (1 - p) ** (2**L - sum(b)) * (1.0 if classifyK(k1, k2, L, np.array(b))[0] else 0.0)
             for b in itertools.product([0, 1], repeat=2**L))
    record("lemma7_telescoping", 1e-12 - abs(md.sum() - pz))

# exact recursion over a wide grid of magnitudes and caps up to 2^12
ds = sorted(set(np.geomspace(1e-3, 0.5, 70).tolist() + [0.25, 0.5]))
for (k1, k2, c1, c2, n1, n2) in [(1.0, 1.0, 85, 149, "lemma7_second_moment", "lemma7_work")]:
    for d in ds:
        for S in (0, 1):
            pr = profile(float(d), S, 12, k1, k2)
            for L in range(13):
                y2, w = moments(pr["e2"], pr["ew"], L)
                sc = min(math.sqrt(2**L), 1 / d)
                record(n1, (c1 * sc - y2) / sc)
                record(n2, (c2 * sc - w) / sc)
                if k1 == 1.0:
                    N = 2**L
                    record("lemma6_error", (min(1.0, (N * d * d) ** -2) - pr["err"][L]))
                    r1 = coupled((N,), float(d), S, 1.0, 1.0)  # cap-N classifier alone
                    record("lemma6_work", (17 * mN(N, d) - r1["emax"]) / (17 * mN(N, d)))


# ---------------- Group R ----------------
def solve_t(w, d, rho):
    lo, hi = 1e-12, 10.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if (w * np.minimum(1, mid**2 / d**2)).sum() < rho:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def obj(w, d, v, h):
    return float((w * np.minimum(v, h * np.sqrt(v) / d)).sum())


for _ in range(400):
    k = int(rng.integers(1, 7))
    w = simplex(k)
    d = rng.uniform(0.005, 0.5, k)
    rho = float(rng.uniform(0.01, 0.95))
    t = solve_t(w, d, rho)
    if abs((w * np.minimum(1, t**2 / d**2)).sum() - rho) > 1e-12:
        continue  # rho not attainable below t <= max d (all mass saturated)
    h = float(t * rng.uniform(0.01, 0.999))
    wstar = np.minimum(1, t**2 / d**2)
    best = obj(w, d, wstar, h)
    for _ in range(60):
        v = rng.uniform(0, 1, k) ** rng.uniform(0.2, 3)
        tot = (w * v).sum()
        if tot > rho:
            v = v * rho / tot
        record("psi_optimizer_atomic", best - obj(w, d, v, h) + 1e-12)

# ---------------- report ----------------
targets = [t for t in json.loads((ROOT / "tools" / "targets.json").read_text())["targets"]
           if t.get("tier", 1) == 2]
names = [t["name"] for t in targets]
missing = [n for n in names if n not in results or counts.get(n, 0) == 0]
bad = [n for n in names if n in results and results[n] < 0]
for n in names:
    if n in results:
        print(f"{n:30s} min margin {results[n]: .4g} checks={counts.get(n, 0)}")
if missing:
    print("UNCHECKED TARGETS:", missing)
if bad:
    print("COUNTEREXAMPLES:", bad)
if missing or bad:
    sys.exit(1)
print(f"\nAll {len(names)} Tier 2 targets numerically consistent.")
