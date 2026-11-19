"""Worst RMS/omega(B^{-1/2}) of the family of Theorem AB.1 over point masses.

For B >= 4 the family runs the calibrated batch at level L, with
4*2^L <= B < 8*2^L, at the calibration scale B/4 = lam*2^L, lam in [1, 2).
Its mean-square error is bias^2 + Var(V)*c/(lam*N) exactly (v6 Lemma 5.1).
For B < 4 it outputs 0 and its RMS error is theta <= 1 = omega(B^{-1/2}).
"""
import math, json, pathlib
import numpy as np
from blind12 import sign_parts, mse_parts

LAMS = [1.0, 1.125, 1.25, 1.375, 1.5, 1.625, 1.75, 1.875, 1.999]
QS = np.linspace(0, 1, 41)
res = []
for L in range(0, 15):
    N = 2 ** L
    xs = np.unique(np.concatenate([np.geomspace(0.02, 40, 70), [0.5 * math.sqrt(N)]]))
    best = (0, None); per_lam = {lam: 0.0 for lam in LAMS}
    for x in xs:
        d = min(0.5, x / math.sqrt(N))
        st = sign_parts(d, L)
        for q in QS:
            for lam in LAMS:
                m = mse_parts([(st, 1.0, q)], L, lam)[0]
                hB = 1 / math.sqrt(4 * lam * N)
                r = math.sqrt(m) / min(1.0, hB / d)
                per_lam[lam] = max(per_lam[lam], r)
                if r > best[0]:
                    best = (r, dict(lam=lam, x=round(float(x), 4), d=round(float(d), 5), q=float(q)))
    print(L, 'sup RMS/omega(B^-1/2) =', round(best[0], 4), best[1],
          '| by lam:', {k: round(v, 3) for k, v in per_lam.items()}, flush=True)
    res.append(dict(L=L, ratio=best[0], arg=best[1], by_lam={str(k): v for k, v in per_lam.items()}))
json.dump(res, open(pathlib.Path(__file__).with_name('scan_scaled.json'), 'w'), indent=1)
