"""Separately written high-precision replay of the package's numerical claims.

Written at integration from the definitions in paper/v6/finite-comparison.tex,
without importing the package module. K is the minimum over all 2^n hard
subsets (lem:hard-selection in paper/v6/entropy-tail-statement.tex), not over
the bandwise-suffix family. mpmath arithmetic is high precision but not
interval arithmetic, so this is a cross-check, not a certificate.
Apache-2.0.
"""
from __future__ import annotations

from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import random
import sys

import mpmath as mp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from runtime_output import compare, output_directory

EVIDENCE = HERE / 'evidence'
OBSTRUCTION = json.loads((HERE / 'obstruction_law.json').read_text())
DIGITS = 15


def real(x) -> mp.mpf:
    """Exact rational to mpf; mpmath 1.3 does not accept Fraction."""
    x = F(x)
    return mp.mpf(x.numerator) / x.denominator


def band(d: F) -> int:
    """Index j of I_j = (2^-(j+2), 2^-(j+1)]."""
    j = 0
    while not F(1, 2 ** (j + 2)) < d <= F(1, 2 ** (j + 1)):
        j += 1
    return j


def entropy(costs) -> mp.mpf:
    a = [x for x in costs if x > 0]
    total = mp.fsum(a)
    return total + mp.fsum(x * mp.log(total / x) for x in a) if a else mp.mpf(0)


def objective(atoms, selected, rho, h) -> mp.mpf:
    costs: dict[int, mp.mpf] = {}
    remainder = mp.mpf(0)
    for (d, w), s in zip(atoms, selected):
        costs[band(d)] = costs.get(band(d), 0) + real(s) * real(w) / real(d) ** 2
        remainder += (1 - real(s)) * real(w) * min(mp.mpf(1), h / real(d))
    return h * mp.sqrt(real(rho) * entropy(costs.values())) + remainder


def k_value(atoms, rho, h):
    values = {bits: objective(atoms, bits, rho, h) for bits in product((0, 1), repeat=len(atoms))}
    best = min(values, key=values.get)
    return min(real(rho), values[best]), list(best)


def q_value(atoms, rho, h) -> mp.mpf:
    left, core = F(rho), []
    for _, w in atoms:
        removed = min(left, w)
        core.append(1 - removed / w)
        left -= removed
    return min(real(rho), objective(atoms, core, rho, h))


def best_global_cut(atoms, rho, h) -> mp.mpf:
    n = len(atoms)
    return min(min(real(rho), objective(atoms, [0] * (n - k) + [1] * k, rho, h))
               for k in range(n + 1))


def law(pairs):
    atoms = sorted((F(d), F(w)) for d, w in pairs)
    assert sum(w for _, w in atoms) == 1 and all(0 < d <= F(1, 2) for d, _ in atoms)
    return atoms


def show(x) -> str:
    return mp.nstr(x, DIGITS)


def examples() -> dict:
    mp.mp.dps = 50
    record = {}
    atoms = law([('0.000215282', '0.413943'), ('0.000316030', '0.014171'),
                 ('0.001250871', '0.094956'), ('0.022545179', '0.021878'),
                 ('0.024956686', '0.450979'), ('0.328605066', '0.004073')])
    h = mp.mpf(152287) / mp.mpf(10) ** 11
    k, argmin = k_value(atoms, F(2113, 10000), h)
    q = q_value(atoms, F(2113, 10000), h)
    record['sqrt2_counterexample'] = {'K': show(k), 'Q': show(q), 'Q_over_K': show(q / k),
                                      'argmin': argmin, 'exceeds_sqrt2': bool(q / k > mp.sqrt(2))}
    atoms = law(OBSTRUCTION['atoms_gap_mass'])
    rho, h = F(OBSTRUCTION['rho']), F(OBSTRUCTION['h'])
    h = real(h)
    k, argmin = k_value(atoms, rho, h)
    q = q_value(atoms, rho, h)
    record['obstruction_1_4604'] = {'K': show(k), 'Q': show(q), 'Q_over_K': show(q / k),
                                    'argmin': argmin, 'exceeds_1_4604': bool(q / k > mp.mpf('1.4604'))}
    atoms = law([('1/4', '9999/10000'), ('1/2', '1/10000')])
    h = mp.mpf(10) ** -4
    k, argmin = k_value(atoms, F(1, 4), h)
    record['not_one_global_threshold'] = {'K': show(k), 'argmin': argmin,
                                          'best_global_cut': show(best_global_cut(atoms, F(1, 4), h))}
    before = k_value(law([('249/1000', '1/2'), ('251/1000', '1/2')]), F(1, 100), h)[0]
    after = k_value(law([('251/1000', 1)]), F(1, 100), h)[0]
    record['cross_boundary'] = {'K_before': show(before), 'K_after': show(after),
                                'ratio': show(before / after)}
    return record


def sweep(trials: int, seed: int) -> dict:
    """Random laws over many bands; checks K <= V <= Q <= (8/5)K numerically."""
    mp.mp.dps = 30
    rng = random.Random(seed)
    slack = 1 + mp.mpf(10) ** -20
    worst, chain_failures = mp.mpf(0), 0
    for _ in range(trials):
        n = rng.randint(1, 7)
        gaps: set[F] = set()
        while len(gaps) < n:
            gaps.add(F(max(1, round(2 ** -rng.uniform(1, 14) * 10 ** 9)), 10 ** 9))
        raw = [rng.randint(1, 1000) for _ in range(n)]
        atoms = law(zip(sorted(gaps), (F(r, sum(raw)) for r in raw)))
        rho = F(rng.randint(1, 2500), 10000)
        h = mp.mpf(2) ** -rng.uniform(2, 20)
        k = k_value(atoms, rho, h)[0]
        v = best_global_cut(atoms, rho, h)
        q = q_value(atoms, rho, h)
        if not (k <= v * slack and v <= q * slack and q <= mp.mpf(8) / 5 * k * slack):
            chain_failures += 1
        worst = max(worst, q / k)
    return {'seed': seed, 'laws': trials, 'chain_failures': chain_failures,
            'max_Q_over_K': show(worst)}


def main() -> int:
    out, writing = output_directory(__doc__, EVIDENCE)
    record = {'scope': 'independent high-precision cross-check, not interval arithmetic or a proof',
              'decimal_digits_shown': DIGITS,
              'examples': examples(), 'random_sweep': sweep(1000, 20261030)}
    (out / 'independent_check.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record, indent=2))
    return 0 if writing else compare(out, ['independent_check.json'], EVIDENCE)


if __name__ == '__main__':
    sys.exit(main())
