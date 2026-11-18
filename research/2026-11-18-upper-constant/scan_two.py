import itertools, math, json, pathlib
import numpy as np
from blind import *

def stats_vec(d, L):
    cs = coin_stats(d, L)
    pl = np.array([p_level(l) for l in range(L + 1)])
    # per sign: (A = P(Z_L=1), S_part, c_part)
    return {s: (cs[s][L, 0], (cs[s][:, 1] / pl).sum(), (pl * cs[s][:, 2]).sum()) for s in (1, -1)}

def mse_fast(parts, L):
    N = 2 ** L
    u = th = S = c = 0.0
    for (st, w, q) in parts:
        for s, ws in ((1, q), (-1, 1 - q)):
            A, Sp, cp = st[s]
            u += w * ws * A; S += w * ws * Sp; c += w * ws * cp
        th += w * q
    c += R ** (L + 1)
    return (u - th) ** 2 + (S - u * u) * c / N

out = []
for L in (4, 6, 8, 10, 12):
    N = 2 ** L
    xs = sorted(set(list(np.geomspace(0.03, 40, 22)) + [0.5 * math.sqrt(N)]))
    ds = sorted(set(min(0.5, x / math.sqrt(N)) for x in xs))
    st = {d: stats_vec(d, L) for d in ds}
    h8 = 1 / math.sqrt(8 * N)
    qg = [0, 0.25, 0.5, 0.75, 1]
    best = (0, None)
    for d1, d2 in itertools.combinations(ds, 2):
        for w in np.geomspace(0.002, 0.998, 20):
            om = w * min(1, h8 / d1) + (1 - w) * min(1, h8 / d2)
            for q1 in qg:
                for q2 in qg:
                    m = mse_fast([(st[d1], w, q1), (st[d2], 1 - w, q2)], L)
                    r = math.sqrt(m) / om
                    if r > best[0]:
                        best = (r, (d1 * math.sqrt(N), d2 * math.sqrt(N), w, q1, q2))
    # point-mass best on same grid for comparison
    pbest = max(math.sqrt(mse_fast([(st[d], 1.0, q)], L)) / min(1, h8 / d) for d in ds for q in qg)
    print(L, 'two-point sup ratio', round(best[0], 3), 'at x1,x2,w,q1,q2 =', tuple(round(float(v), 4) for v in best[1]), '| point-mass on same grid', round(pbest, 3), flush=True)
    out.append(dict(L=L, two_point=best[0], arg=[float(v) for v in best[1]], point=pbest))
json.dump(out, open(pathlib.Path(__file__).with_name('scan_two.json'), 'w'), indent=1)
