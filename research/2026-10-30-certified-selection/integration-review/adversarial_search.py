"""Float64 adversarial search for large Q/K; exploration only, not a certificate.

Usage: python adversarial_search.py N SEED STARTS [--output-dir DIR]
Nelder-Mead from STARTS random points over N atoms (log-gaps, mass logits,
rho and h), maximizing Q/K computed over all 2^N hard subsets. The best point
is rounded to 12 decimal places and written as a candidate law. Only
certify_obstruction.py gives a candidate certificate status.
`8 7 120` produced obstruction_law.json. For some N the search wanders to
gaps near 1e-160, where float64 overflows and the reported ratio is
meaningless; such outputs are discarded, never certified. Apache-2.0.
"""
from __future__ import annotations

from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import sys
import warnings

import numpy as np
from scipy.optimize import minimize

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from runtime_output import output_directory

warnings.filterwarnings('ignore')
DECIMALS = 10**12


def decode(x, n):
    gaps = np.exp(-np.abs(x[:n]) - np.log(2.0))
    w = np.exp(x[n:2 * n] - x[n:2 * n].max())
    w /= w.sum()
    rho = 0.25 / (1 + np.exp(-x[2 * n]))
    h = np.exp(-abs(x[2 * n + 1]))
    return gaps, w, rho, h


def entropy(costs):
    total = costs.sum(-1, keepdims=True)
    with np.errstate(divide='ignore', invalid='ignore'):
        terms = np.where(costs > 0, costs * np.log(total / costs), 0.0)
    return total[..., 0] + terms.sum(-1)


def ratio(x, n, subsets):
    gaps, w, rho, h = decode(x, n)
    order = np.argsort(gaps)
    gaps, w = gaps[order], w[order]
    bands = np.maximum(np.floor(-np.log2(gaps) - 1 + 1e-12).astype(int), 0)
    onehot = (bands[:, None] == np.unique(bands)[None, :]).astype(float)
    alpha = w / gaps**2
    ordinary = w * np.minimum(1.0, h / gaps)
    objective = h * np.sqrt(rho * entropy((subsets * alpha) @ onehot)) \
        + ((1 - subsets) * ordinary).sum(-1)
    k = min(rho, objective.min())
    left, core = rho, np.ones(n)
    for i in range(n):
        removed = min(left, w[i])
        core[i] = 1 - removed / w[i]
        left -= removed
    q = min(rho, h * np.sqrt(rho * entropy(((core * alpha) @ onehot)[None, :]))[0]
            + ((1 - core) * ordinary).sum())
    return q / k if k > 0 else 1.0


def search(n, seed, starts):
    subsets = np.array(list(product((0, 1), repeat=n)), dtype=float)
    rng = np.random.default_rng(seed)
    best = (0.0, None)
    for _ in range(starts):
        x0 = np.concatenate([rng.uniform(0, 10, n), rng.normal(0, 2, n),
                             rng.normal(0, 2, 1), rng.uniform(2, 12, 1)])
        result = minimize(lambda x: -ratio(x, n, subsets), x0, method='Nelder-Mead',
                          options={'maxiter': 4000, 'xatol': 1e-10, 'fatol': 1e-12})
        if -result.fun > best[0]:
            best = (-result.fun, result.x)
    return best


def rounded(value) -> F:
    return F(round(float(value) * DECIMALS), DECIMALS)


def main() -> int:
    n, seed, starts = (int(a) for a in sys.argv[1:4])
    del sys.argv[1:4]
    out, _ = output_directory(__doc__)
    float_ratio, x = search(n, seed, starts)
    gaps, w, rho, h = decode(x, n)
    masses = [rounded(v) for v in w]
    masses[-1] += 1 - sum(masses)
    atoms = sorted(zip((rounded(g) for g in gaps), masses))
    candidate = {'scope': 'float64 exploration output; not a certificate',
                 'arguments': {'N': n, 'seed': seed, 'starts': starts},
                 'float_Q_over_K': float_ratio,
                 'atoms_gap_mass': [[str(g), str(m)] for g, m in atoms],
                 'rho': str(rounded(rho)), 'h': str(rounded(h))}
    known = json.loads((HERE / 'obstruction_law.json').read_text())
    same = all(candidate[k] == known[k] for k in ('atoms_gap_mass', 'rho', 'h'))
    path = out / f'adversarial_N{n}_seed{seed}_starts{starts}.json'
    path.write_text(json.dumps(candidate, indent=2) + '\n')
    print(json.dumps(candidate, indent=2))
    print(f'wrote {path}; matches obstruction_law.json: {same}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
