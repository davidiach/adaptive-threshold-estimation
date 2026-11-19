"""Large-budget limit of the family of Theorem AB.1, for several thresholds.

The family runs one level L at the calibration scale B/4. By v6 Lemma 5.1 its
mean-square error is bias^2 + Var(V)*c/(B/4). Fix a gap law with finitely many
atoms and let B grow. For b > 1/4 the bias falls faster than
omega(B^{-1/2}) = B^{-1/2}*E[1/D], and Var(V) and c tend to their sums over
all levels, so

    RMS / omega(B^{-1/2})  ->  2*sqrt(Var V * c) / E[1/D].

This is independent of lam = B/(4*2^L). For a point mass it is
2*d*sqrt(Var V * c). The script evaluates it for point masses and two-point
laws, with sign fractions per atom, on a grid of gaps.

It also gives the sharp per-gap constants of the proof route in this limit:
sigma* = sup d*E V^2 and kappa* = sup d*c over the gap and the sign, and
P* = sup over two-point laws of E V^2 * c / E[1/D]^2. A proof that bounds
E V^2 <= sigma*A and c <= kappa*A separately can do no better than
sigma* * kappa*; one that bounds the product directly, no better than P*.

Levels are summed to ceil(log2(1/d^2)) + 36; the truncated tail is below
1e-4 in every quantity. Floating point; not a proof.
"""
import json, math, pathlib, sys
from multiprocessing import Pool
import numpy as np
from blind12 import sign_parts

CANDIDATES = [(1.0, 1.0), (1.5, 1.0), (2.0, 0.5), (2.0, 0.75), (2.5, 0.5), (3.0, 0.5)]
DS = [float(d) for d in np.geomspace(0.005, 0.5, 36)]
QS2 = np.linspace(0, 1, 5)
WS = np.linspace(0.005, 0.995, 199)
EXTRA = 36


def one(job):
    a, b, d = job
    L = math.ceil(math.log2(1 / d ** 2)) + EXTRA
    st = sign_parts(d, L, a, b)
    return dict(a=a, b=b, d=d, L=L,
                plus=[float(x) for x in st[1]], minus=[float(x) for x in st[-1]])


def mix(row, q):
    """(P(Z=1), E V^2, c) of one atom with sign fraction q."""
    return q * np.array(row['plus']) + (1 - q) * np.array(row['minus'])


def analyse(rows):
    out = {}
    # point masses
    best_pm = (0, None)
    qs = np.linspace(0, 1, 101)
    for r in rows:
        d = r['d']
        for q in qs:
            u, S, c = mix(r, q)
            val = 2 * d * math.sqrt(max(S - u * u, 0) * c)
            if val > best_pm[0]:
                best_pm = (val, dict(d=d, q=float(q)))
    out['point_mass_limit'] = best_pm[0]; out['point_mass_arg'] = best_pm[1]
    # per-gap constants
    sig = max((r['d'] * max(r['plus'][1], r['minus'][1]), r['d']) for r in rows)
    kap = max((r['d'] * max(r['plus'][2], r['minus'][2]), r['d']) for r in rows)
    out['sigma_star'], out['sigma_star_d'] = sig
    out['kappa_star'], out['kappa_star_d'] = kap
    # two-point laws
    best2 = (0, None); bestP = (0, None)
    w = WS
    for i in range(len(rows)):
        for j in range(i + 1, len(rows)):
            ri, rj = rows[i], rows[j]
            Ainv = w / ri['d'] + (1 - w) / rj['d']
            for qi in QS2:
                ui, Si, ci = mix(ri, qi)
                for qj in QS2:
                    uj, Sj, cj = mix(rj, qj)
                    u = w * ui + (1 - w) * uj
                    S = w * Si + (1 - w) * Sj
                    c = w * ci + (1 - w) * cj
                    ratio = 2 * np.sqrt(np.maximum(S - u * u, 0) * c) / Ainv
                    k = int(np.argmax(ratio))
                    if ratio[k] > best2[0]:
                        best2 = (float(ratio[k]), dict(d=[ri['d'], rj['d']], q=[float(qi), float(qj)], w=float(w[k])))
                    P = S * c / Ainv ** 2
                    k = int(np.argmax(P))
                    if P[k] > bestP[0]:
                        bestP = (float(P[k]), dict(d=[ri['d'], rj['d']], q=[float(qi), float(qj)], w=float(w[k])))
    out['two_point_limit'] = max(best2[0], best_pm[0])
    out['two_point_arg'] = best2[1] if best2[0] > best_pm[0] else 'point mass'
    # a point mass is a two-point law with equal atoms
    pm_P = max(r['d'] ** 2 * max(r['plus'][1] * r['plus'][2], r['minus'][1] * r['minus'][2]) for r in rows)
    out['P_star'] = max(bestP[0], pm_P); out['P_star_arg'] = bestP[1] if bestP[0] >= pm_P else 'point mass'
    for beta in (1.0, 0.5):
        tag = 'beta1' if beta == 1.0 else 'beta_half'
        out[f'route_per_gap_{tag}'] = math.sqrt(4 * (2 * beta ** 2 + out['sigma_star'] * out['kappa_star']))
        out[f'route_joint_{tag}'] = math.sqrt(4 * (2 * beta ** 2 + out['P_star']))
    return out


if __name__ == "__main__":
    jobs = [(a, b, d) for a, b in CANDIDATES for d in sorted(DS)]
    with Pool(4) as pool:
        rows = pool.map(one, jobs, chunksize=1)
    res = []
    for a, b in CANDIDATES:
        rs = [r for r in rows if r['a'] == a and r['b'] == b]
        for r in rs:
            d = r['d']
            print(f"a={a} b={b} d={d:.4f} L={r['L']}  +: P(Z=1)={r['plus'][0]:.6f} d*EV2={d*r['plus'][1]:.4f} "
                  f"d*c={d*r['plus'][2]:.4f}  -: P(Z=1)={r['minus'][0]:.2e} d*EV2={d*r['minus'][1]:.4f} "
                  f"d*c={d*r['minus'][2]:.4f}", flush=True)
        an = analyse(rs)
        print(f"== a={a} b={b}: limit ratio point mass {an['point_mass_limit']:.4f} {an['point_mass_arg']}, "
              f"two-point {an['two_point_limit']:.4f} {an['two_point_arg']}; sigma*={an['sigma_star']:.4f} "
              f"(d={an['sigma_star_d']:.4f}) kappa*={an['kappa_star']:.4f} (d={an['kappa_star_d']:.4f}) "
              f"P*={an['P_star']:.4f} {an['P_star_arg']}; route per gap beta=1/2: {an['route_per_gap_beta_half']:.3f}, "
              f"joint beta=1/2: {an['route_joint_beta_half']:.3f}", flush=True)
        res.append(dict(a=a, b=b, rows=rs, **an))
    json.dump(res, open(pathlib.Path(__file__).with_name('limit12.json'), 'w'), indent=1)
