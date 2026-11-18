import math, pathlib, sys, json, numpy as np
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / 'toolkit'))
from threshold_toolkit.planner import GuessedRates, simulate
out = []
for L, runs in ((8, 12000), (10, 4000)):
    N = 2 ** L; budget = 4 * N
    best = (0, None)
    for d in (0.03, 0.06, 0.1, 0.15, 0.2, 0.3, 0.5):
        for q in (1.0, 0.8, 0.5):
            if q == 1.0: rates = [0.5 + d]
            elif q == 0.5: rates = [0.5 + d, 0.5 - d]
            else: rates = [0.5 + d] * 4 + [0.5 - d]
            sim = simulate(GuessedRates(rates), budget, runs=runs, seed=11)
            om8 = min(1.0, 1 / (d * math.sqrt(8 * N)))
            omN = min(1.0, 1 / (d * math.sqrt(N)))
            r8 = sim.rms_error / om8
            out.append(dict(L=L, runs=runs, d=d, q=q, clipped=sim.rms_error, raw=sim.raw_rms_error, ratio_8N=r8, ratio_N=sim.rms_error / omN))
            if r8 > best[0]: best = (r8, (d, q, sim.rms_error, sim.rms_error / omN))
    print(L, 'clipped sup RMS/omega(1/sqrt(8N)) ~', round(best[0], 3), 'at (d, q, RMS, ratio vs omega(1/sqrt N))', tuple(round(x, 3) for x in best[1]), flush=True)
json.dump(out, open(pathlib.Path(__file__).with_name('clipped.json'), 'w'), indent=1)
