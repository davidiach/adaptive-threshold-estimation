"""Scoping: which one-coin bounds would bring the RMS upper constant to 8?

The proof of the constant 12 has MSE <= (8*beta^2 + 4*sigma*kappa) omega^2,
with beta the bias constant (Lean: 1), sigma and kappa the call
second-moment and cost constants (Lean: 13/2 and 26/5). This script computes
sigma and kappa for a ladder of one-coin bounds, all for the estimator of
the paper (thresholds a = b = 1), positive sign (the worse one for the tie
rule):

1. the method's limits with tail proxies (tails.py): Hoeffding, Mills,
   'sharp' (Mills plus the tangent at 0), Gaussian;
2. the method at fixed gaps with rigorous lattice bounds (rigorous.py):
   Hoeffding-or-Bahadur, and in addition the median bound;
3. the exact one-coin quantities, from
   ../2026-11-19-upper-constant-12/limit12.json;
4. where the second-moment bound loses, by bands of x = 2^l d^2;
5. hybrids: the rigorous bounds below a gap d0, exact values above it;
6. a check of rigorous.py: with Hoeffding alone it must approach the
   Hoeffding limits of tails.py as the gap shrinks.

Writes scope.json. Floating point; not a proof.
"""
import json, math, pathlib
import numpy as np
from multiprocessing import Pool
import tails, rigorous
from blind12 import level_stats

HERE = pathlib.Path(__file__).parent
DS = [float(d) for d in np.geomspace(0.002, 0.5, 49)]
BANDS = [(0, 0.25), (0.25, 1), (1, 4), (4, 16), (16, math.inf)]


def C(beta2_term, prod):
    return math.sqrt(beta2_term + 4 * prod)


def routes(sigma, kappa):
    P = sigma * kappa
    return dict(sigma=sigma, kappa=kappa, product=P, C_beta1=C(8, P), C_beta_half=C(2, P),
                room8_beta1=14 / P - 1, room8_beta_half=15.5 / P - 1,
                room9_beta1=18.25 / P - 1, room9_beta_half=19.75 / P - 1)


def proxy(kind):
    kc = tails.kappa_curve(kind, grid=200)
    us, sc = tails.sigma_curve(kind, octaves=40, per=24)
    i = int(sc.argmax())
    return kind, dict(kappa=float(kc.max()), sigma=float(sc[i]), sigma_at_d=float(math.sqrt(us[i])),
                      sigma_small_d=float(sc[-24:].max()))


def rig(job):
    d, central = job
    return dict(d=d, central=central, sigma=rigorous.sigma_at(d, central=central),
                kappa=rigorous.kappa_at(d, central=central))


def band_sums(x, w):
    out = []
    for lo, hi in BANDS:
        m = (x >= lo) & (x < hi)
        out.append(float((2 + math.sqrt(2)) * (np.sqrt(x[m]) * w[m]).sum()))
    return out


def decomposition(d):
    u = d * d
    rows = {}
    for kind in ('hoeffding', 'mills', 'gauss'):
        rows[f'limit form, {kind}'] = band_sums(*tails.sigma_levels(u, kind))
    for central in (False, True):
        rows['rigorous' + (', central' if central else '')] = band_sums(*rigorous.sigma_levels(d, central=central))
    x, w = [], []
    l = 0
    while u * 2 ** l <= 4000:
        x.append(u * 2 ** l); w.append(level_stats(0.5 + d, l)[1]); l += 1
    rows['exact'] = band_sums(np.array(x), np.array(w))
    return rows


if __name__ == "__main__":
    out = {}
    with Pool(4) as pool:
        prox = dict(pool.map(proxy, ['hoeffding', 'mills', 'sharp', 'gauss']))
        rig_rows = pool.map(rig, [(d, c) for c in (False, True) for d in DS], chunksize=1)
    out['proxies'] = prox
    for k, v in prox.items():
        print(f"limit, {k:9s}: kappa={v['kappa']:.4f} sigma={v['sigma']:.4f} (at d={v['sigma_at_d']:.3f}; "
              f"small d {v['sigma_small_d']:.4f})", flush=True)
    out['rigorous'] = rig_rows
    for r in rig_rows:
        print(f"rigorous{' +central' if r['central'] else '         '} d={r['d']:.4f}: sigma={r['sigma']:.4f} "
              f"kappa={r['kappa']:.4f}", flush=True)

    exact = json.load(open(HERE.parent / '2026-11-19-upper-constant-12' / 'limit12.json'))
    ex = [r for r in exact if r['a'] == 1.0 and r['b'] == 1.0][0]['rows']
    ex_rows = [dict(d=r['d'], sigma=r['d'] * max(r['plus'][1], r['minus'][1]),
                    kappa=r['d'] * max(r['plus'][2], r['minus'][2])) for r in ex]
    out['exact'] = ex_rows

    ladder = {}
    for k in ('hoeffding', 'mills', 'sharp', 'gauss'):
        ladder[f'limit, {k}'] = routes(prox[k]['sigma'], prox[k]['kappa'])
    for central in (False, True):
        rs = [r for r in rig_rows if r['central'] == central]
        ladder['rigorous' + (' + median' if central else '')] = routes(max(r['sigma'] for r in rs),
                                                                      max(r['kappa'] for r in rs))
    ladder['exact'] = routes(max(r['sigma'] for r in ex_rows), max(r['kappa'] for r in ex_rows))
    ladder['Lean'] = routes(13 / 2, 26 / 5)
    out['ladder'] = ladder
    print("\nladder: sigma kappa product | C(beta=1) C(beta=1/2) | room for 8 (beta=1, 1/2) | room for 9", flush=True)
    for k, v in ladder.items():
        print(f"  {k:22s} {v['sigma']:.3f} {v['kappa']:.3f} {v['product']:6.2f} | {v['C_beta1']:.2f} "
              f"{v['C_beta_half']:.2f} | {v['room8_beta1']:+.1%} {v['room8_beta_half']:+.1%} | "
              f"{v['room9_beta1']:+.1%} {v['room9_beta_half']:+.1%}", flush=True)

    hyb = []
    for central in (False, True):
        rs = [r for r in rig_rows if r['central'] == central]
        for d0 in (0.01, 0.02, 0.05, 0.1, 0.2):
            s = max([r['sigma'] for r in rs if r['d'] < d0] + [r['sigma'] for r in ex_rows if r['d'] >= d0])
            k = max([r['kappa'] for r in rs if r['d'] < d0] + [r['kappa'] for r in ex_rows if r['d'] >= d0])
            row = dict(central=central, d0=d0, **routes(s, k))
            hyb.append(row)
            print(f"hybrid{' +median' if central else '        '} d0={d0}: sigma={s:.3f} kappa={k:.3f} "
                  f"C(beta=1)={row['C_beta1']:.2f} C(beta=1/2)={row['C_beta_half']:.2f}", flush=True)
    out['hybrid'] = hyb

    dec = {}
    for d in (0.01, 0.2):
        dec[str(d)] = decomposition(d)
        print(f"\nsecond-moment bound by band of x at d={d}: " + " ".join(f"[{lo},{hi})" for lo, hi in BANDS), flush=True)
        for k, v in dec[str(d)].items():
            print(f"  {k:28s} " + " ".join(f"{t:6.3f}" for t in v) + f"  total {sum(v):.3f}", flush=True)
    out['decomposition'] = dec

    rigorous.USE_BAHADUR = False
    chk = [dict(d=d, sigma=rigorous.sigma_at(d), kappa=rigorous.kappa_at(d)) for d in (0.05, 0.01, 0.002)]
    rigorous.USE_BAHADUR = True
    out['hoeffding_check'] = chk
    print("\ncheck, rigorous.py with Hoeffding alone (limits: sigma %.4f, kappa %.4f):" %
          (prox['hoeffding']['sigma'], prox['hoeffding']['kappa']), flush=True)
    for r in chk:
        print(f"  d={r['d']}: sigma={r['sigma']:.4f} kappa={r['kappa']:.4f}", flush=True)
    json.dump(out, open(HERE / 'scope.json', 'w'), indent=1)
