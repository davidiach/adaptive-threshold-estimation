import math, json, pathlib
import numpy as np
from blind import *
res = []
qs = np.linspace(0, 1, 41)
for L in range(0, 15):
    N = 2 ** L
    best8 = (0, None); bestN = (0, None)
    xs = np.unique(np.concatenate([np.geomspace(0.02, 40, 70), [0.5*math.sqrt(N)]]))
    for x in xs:
        d = min(0.5, x / math.sqrt(N))
        for q in qs:
            m, b, v, pi = mse([(d, 1.0, q)], L)
            rms = math.sqrt(m)
            r8 = rms / min(1.0, (1 / math.sqrt(8 * N)) / d)
            rN = rms / min(1.0, (1 / math.sqrt(N)) / d)
            if r8 > best8[0]: best8 = (r8, (round(float(x), 4), round(float(d), 5), float(q), float(rms)))
            if rN > bestN[0]: bestN = (rN, (round(float(x), 4), round(float(d), 5), float(q), float(rms)))
    print(L, 'sup RMS/omega(1/sqrt(8N)) =', round(best8[0], 3), best8[1], '| sup RMS/omega(1/sqrt N) =', round(bestN[0], 3), bestN[1], flush=True)
    res.append(dict(L=L, ratio_8N=best8[0], arg_8N=best8[1], ratio_N=bestN[0], arg_N=bestN[1]))
json.dump(res, open(pathlib.Path(__file__).with_name('scan_point.json'), 'w'), indent=1)
