import json, math, pathlib, sys
import numpy as np
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / 'toolkit'))
from threshold_toolkit.planner import GuessedRates, simulate
from blind import mse
rows = []
for L, d, pos in [(6, 0.3, 1.0), (6, 0.05, 0.5), (8, 0.2, 1.0), (8, 0.02, 0.5), (10, 0.12, 1.0)]:
    N = 2 ** L
    budget = 4 * N  # budget_level(4N) = L
    rates = [0.5 + d] if pos == 1.0 else [0.5 + d, 0.5 - d]
    pop = GuessedRates(rates)
    exact = math.sqrt(mse([(d, 1.0, pos)], L)[0])
    sim = simulate(pop, budget, runs=40000, seed=7)
    rows.append(dict(L=L, d=d, q=pos, exact_raw_rms=exact, simulated_raw_rms=sim.raw_rms_error, simulated_clipped_rms=sim.rms_error, mean_flips=sim.mean_flips, budget=budget, runs=40000))
    print(f"L={L} d={d} q={pos}: exact raw RMS={exact:.4f}  simulated raw RMS={sim.raw_rms_error:.4f}  clipped RMS={sim.rms_error:.4f}  mean flips={sim.mean_flips:.1f} (budget {budget})", flush=True)
json.dump(rows, open(pathlib.Path(__file__).with_name('crosscheck.json'), 'w'), indent=1)
