"""Finite-budget checks of the family of Theorem AB.1.

1. Two-point gap laws for the paper's thresholds (a = b = 1), against point
   masses on the same coarse grid of gaps.
2. Point masses for retuned thresholds, as in scan_scaled.py but on a coarser
   grid, to see how fast they approach their large-budget limits.
3. The sharp bias constants: beta_L = sup_d err_L(d)/min(1, 2^{-L/2}/d), the
   constant of the bound bias <= beta*omega(2^{-L/2}) that the proof uses with
   beta = 1, and beta_B = sup_d err_L(d)/min(1, B^{-1/2}/d), the constant of a
   bound against omega(B^{-1/2}) directly. Here err_L(d) is the larger of the
   two wrong-label probabilities of the level-L classifier at gap d.

The ratio is RMS / omega(B^{-1/2}) with B = 4*lam*2^L, from the exact formula
bias^2 + Var(V)*c/(lam*2^L) of v6 Lemma 5.1. Floating point; not a proof.
"""
import itertools, json, math, pathlib
import numpy as np
from blind12 import sign_parts, mse_parts, level_stats

LAMS = [1.0, 1.5, 1.999]


def ratio(parts, atoms, L, lam):
    hB = 1 / math.sqrt(4 * lam * 2 ** L)
    om = sum(w * min(1.0, hB / d) for d, w in atoms)
    return math.sqrt(mse_parts(parts, L, lam)[0]) / om


def two_point(L, a=1.0, b=1.0):
    N = 2 ** L
    xs = np.geomspace(0.05, 20, 16)
    ds = sorted({min(0.5, float(x) / math.sqrt(N)) for x in xs})
    st = {d: sign_parts(d, L, a, b) for d in ds}
    best1 = (0, None); best2 = (0, None)
    for d in ds:
        for q in np.linspace(0, 1, 21):
            for lam in LAMS:
                r = ratio([(st[d], 1.0, q)], [(d, 1.0)], L, lam)
                if r > best1[0]:
                    best1 = (r, dict(d=d, q=float(q), lam=lam))
    for d1, d2 in itertools.combinations(ds, 2):
        for q1, q2 in itertools.product((0.0, 0.5, 1.0), repeat=2):
            for w in np.linspace(0.05, 0.95, 19):
                for lam in LAMS:
                    r = ratio([(st[d1], w, q1), (st[d2], 1 - w, q2)], [(d1, w), (d2, 1 - w)], L, lam)
                    if r > best2[0]:
                        best2 = (r, dict(d=[d1, d2], q=[q1, q2], w=float(w), lam=lam))
    return best1, best2


def point_masses(L, a, b):
    N = 2 ** L
    best = (0, None)
    for x in np.geomspace(0.05, 40, 40):
        d = min(0.5, float(x) / math.sqrt(N))
        st = sign_parts(d, L, a, b)
        for q in np.linspace(0, 1, 21):
            for lam in LAMS:
                r = ratio([(st, 1.0, q)], [(d, 1.0)], L, lam)
                if r > best[0]:
                    best = (r, dict(d=d, q=float(q), lam=lam))
    return best


def bias_constants(L, a, b):
    N = 2 ** L
    best = dict(beta_L=(0, None), **{f"beta_B_lam{lam}": (0, None) for lam in LAMS})
    for x in np.geomspace(0.001, 40, 160):
        d = min(0.5, float(x) / math.sqrt(N))
        up = level_stats(0.5 + d, L, a, b)[0]
        down = level_stats(0.5 - d, L, a, b)[0]
        err = max(1 - up, down)
        for key, h in [("beta_L", 1 / math.sqrt(N))] + [(f"beta_B_lam{lam}", 1 / math.sqrt(4 * lam * N)) for lam in LAMS]:
            r = err / min(1.0, h / d)
            if r > best[key][0]:
                best[key] = (r, round(float(x), 4))
    return best


if __name__ == "__main__":
    out = dict(two_point=[], retuned=[], bias=[])
    for a, b in ((1.0, 1.0), (2.5, 0.5)):
        for L in (6, 10, 14):
            bc = bias_constants(L, a, b)
            print(f"a={a} b={b} L={L}: " + ", ".join(f"{k}={v[0]:.4f} (x={v[1]})" for k, v in bc.items()), flush=True)
            out['bias'].append(dict(a=a, b=b, L=L, **{k: v[0] for k, v in bc.items()},
                                    args={k: v[1] for k, v in bc.items()}))
    for L in (4, 6, 8, 10, 12):
        b1, b2 = two_point(L)
        print(f"a=b=1 L={L}: point masses {b1[0]:.4f} {b1[1]} | two-point laws {b2[0]:.4f} {b2[1]}", flush=True)
        out['two_point'].append(dict(L=L, point_mass=b1[0], point_mass_arg=b1[1], two_point=b2[0], two_point_arg=b2[1]))
    for a, b in ((1.0, 1.0), (2.0, 0.5), (2.5, 0.5), (3.0, 0.5)):
        for L in (6, 10, 14):
            r = point_masses(L, a, b)
            print(f"a={a} b={b} L={L}: point masses {r[0]:.4f} {r[1]}", flush=True)
            out['retuned'].append(dict(a=a, b=b, L=L, ratio=r[0], arg=r[1]))
    json.dump(out, open(pathlib.Path(__file__).with_name('scan_finite.json'), 'w'), indent=1)
