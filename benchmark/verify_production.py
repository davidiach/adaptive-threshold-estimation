"""Replay checks of the production direct-real routines.

verify_real.py, locked in results/real_selection.json, compares tape copies of
the stopping state machines (tape_pair, antithetic_tape, sum_tape) with an
independent classifier. Of the production routines it checks only level_count's
budget bound and that real_replicates matches separately seeded real_estimate
calls. This script checks the production routines in real_threshold.py. It
reseeds Numba's generator, replays the exact draws each routine makes, and checks:

- real_pair, antithetic_pair, sum_term and real_term against an independent
  scalar classifier on the replayed tape: every value and cost, the level draw,
  real_term's 1/p_J weighting in the pair modes, sum_term's 1/P(J>=k) weights,
  and that each call drew exactly the observations it billed;
- every recorded tuning cell in its own mode, at its deepest level, and every
  trained level of every recorded training configuration;
- train_level against consecutive production pair calls, and two recorded
  training rows reproduced exactly from their seeds;
- real_estimate's two-success calibration and real_replicates' repeats,
  re-derived from the classifier-checked real_term;
- level_count, and the level law of each selected configuration.

It needs the locked results/ records. These are implementation checks, not
statistical error guarantees.
"""
from __future__ import annotations
import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if (ROOT/'.runtime/python').exists():sys.path.insert(0, str(ROOT/'.runtime/python'))
import numpy as np
from numba import njit
import real_threshold as rt
from reference import real_x, seed_rng

MINIMUM = 16  # the production default, and the value sum_term hard-codes
# (start, ratio, threshold, deepest level) with caps up to 4096 flips.
CONFIGS = [(16, 2, 1.0, 4), (64, 4, 0.5, 2), (256, 2, 1.5, 3), (1024, 4, 1.0, 1)]
SEEDS = range(20261029, 20261029+120)
LEVEL_SEEDS = range(20261200, 20261200+4000)  # searched for seeds that draw a given level


@njit
def uniform():
    return np.random.random()


@njit
def normal():
    return np.random.normal()


@njit
def sentinels():
    # Normals are generated in cached pairs, so check one of each kind.
    return np.random.normal(), np.random.random()


@njit
def observations(y, count):
    xs = np.empty(count)
    for i in range(count):
        xs[i] = real_x(y)
    return xs


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def classify(xs, cap, threshold):
    """Decision and stopping prefix of one capped classifier on xs.

    Checkpoints are prefixes 1, 2, 4, ...; it stops at the cap, or from
    MINIMUM on once the mean clears the sample-variance boundary.
    """
    total = sumsq = 0.0
    used, n = 0, 1
    while True:
        for x in xs[used:n]:
            total += x
            sumsq += x*x
        used = n
        if n >= cap:
            return int(total > 0), n
        if n >= MINIMUM:
            variance = max(0.0, (sumsq-total*total/n)/(n-1))
            if abs(total/n) > threshold*math.sqrt(variance*(1+math.log(cap/n))/n):
                return int(total > 0), n
        n *= 2


def level_from(u, probabilities):
    cumulative = 0.0
    for k, p in enumerate(probabilities):
        cumulative += p
        if u < cumulative:
            return k
    return len(probabilities)-1


def expected_pair(xs, j, start, ratio, threshold, antithetic):
    cap = start*ratio**j
    fine, fine_n = classify(xs, cap, threshold)
    if j == 0:
        return float(fine), fine_n
    coarse = cap//ratio
    if not antithetic:
        z, n = classify(xs, coarse, threshold)
        return float(fine-z), max(fine_n, n)
    # Block b holds observations b, b+ratio, ...; its m-th one arrives at flip
    # b+(m-1)*ratio+1, and the call ends at the first doubled prefix covering all.
    blocks = [classify(xs[b::ratio], coarse, threshold) for b in range(ratio)]
    needed = max([fine_n]+[b+(m-1)*ratio+1 for b, (_, m) in enumerate(blocks)])
    return fine-sum(z for z, _ in blocks)/ratio, 1 << (needed-1).bit_length()


def expected_sum(xs, j, start, ratio, threshold, probabilities):
    zs, ns = zip(*(classify(xs, start*ratio**k, threshold) for k in range(j+1)))
    value = float(zs[0])
    for k in range(1, j+1):
        value += (zs[k]-zs[k-1])/probabilities[k:].sum()
    return value, max(ns)


def replay_pair(seed, j, start, ratio, threshold, antithetic):
    seed_rng(seed)
    return expected_pair(observations(normal(), start*ratio**j), j, start, ratio, threshold, antithetic)


def replay_term(seed, start, ratio, threshold, probabilities, antithetic, sum_mode):
    """Expected real_term output, from the same seeded draws."""
    seed_rng(seed)
    j = level_from(uniform(), probabilities)
    xs = observations(normal(), start*ratio**j)
    if sum_mode:
        return expected_sum(xs, j, start, ratio, threshold, probabilities)
    value, n = expected_pair(xs, j, start, ratio, threshold, antithetic)
    return value/probabilities[j], n


def same(actual, expected, what):
    value, cost = actual
    require(abs(value-expected[0]) <= 1e-12*max(1.0, abs(expected[0])) and cost == expected[1],
            f"{what}: production {actual} != reference {expected}")


def check_call(what, seed, production, args, expected, level_draw):
    """Compare one production call with its replay, and require that it drew
    exactly what it billed: the level uniform, the latent normal and `cost` observations."""
    seed_rng(seed)
    actual = production(*args)
    after = sentinels()
    same(actual, expected, what)
    seed_rng(seed)
    if level_draw:
        uniform()
    observations(normal(), int(actual[1]))
    require(sentinels() == after, f"{what}: production drew observations it did not bill")


def pair_routine(antithetic):
    return rt.antithetic_pair if antithetic else rt.real_pair


def check_pairs(training):
    cases = [(start, ratio, threshold, j, antithetic, seed)
             for start, ratio, threshold, deepest in CONFIGS for j in range(deepest+1)
             for antithetic in (False, True) for seed in SEEDS]
    # Every trained level of every recorded configuration, in its own mode.
    cases += [(cfg['start'], cfg['ratio'], cfg['threshold'], level['level'], cfg.get('antithetic', False),
               SEEDS[0]+row['index'])
              for row in training['rows'] for level in row['levels'] for cfg in [row['config']]]
    for start, ratio, threshold, j, antithetic, seed in cases:
        pair = pair_routine(antithetic)
        check_call(f"{pair.__name__}{(j, start, ratio, threshold)} seed {seed}", seed, pair,
                   (j, start, ratio, threshold), replay_pair(seed, j, start, ratio, threshold, antithetic), False)
    return len(cases)


def check_term(start, ratio, threshold, p, antithetic, sum_mode, seed):
    check_call(f"real_term{(start, ratio, threshold, p.tolist(), antithetic, sum_mode)} seed {seed}", seed,
               rt.real_term, (start, ratio, threshold, p, antithetic, sum_mode),
               replay_term(seed, start, ratio, threshold, p, antithetic, sum_mode), True)


def check_terms(selected):
    """real_term in every mode; sum mode is sum_term."""
    laws = [(start, ratio, threshold, np.full(deepest+1, 1/(deepest+1)))
            for start, ratio, threshold, deepest in CONFIGS]
    laws += [(16, 2, 1.0, np.array([.4, .3, .2, .1])), (64, 4, .5, np.array([.7, .2, .1]))]
    laws += selected
    checks = 0
    for start, ratio, threshold, p in laws:
        for antithetic, sum_mode in ((False, False), (True, False), (False, True)):
            for seed in SEEDS:
                check_term(start, ratio, threshold, p, antithetic, sum_mode, seed)
                checks += 1
    return checks


def check_tuning_cells(tuning):
    """Each distinct recorded tuning cell, in its own mode, at its deepest and middle levels."""
    first_uniform = []
    for seed in LEVEL_SEEDS:
        seed_rng(seed)
        first_uniform.append(uniform())
    cells = {}
    for row in tuning['rows']:
        cfg = row['config']
        cells[(json.dumps(cfg, sort_keys=True), tuple(row['probabilities']))] = (cfg, np.array(row['probabilities']))
    checks = 0
    for cfg, p in cells.values():
        for level in sorted({len(p)-1, (len(p)-1)//2}):
            seed = next((s for s, u in zip(LEVEL_SEEDS, first_uniform) if level_from(u, p) == level), None)
            require(seed is not None, f"no search seed draws level {level} of tuning cell {cfg}")
            check_term(cfg['start'], cfg['ratio'], cfg['threshold'], p, cfg.get('antithetic', False),
                       cfg.get('sum_mode', False), seed)
            checks += 1
    return checks


def check_training(training):
    """train_level rows are consecutive production pair calls, and recorded rows reproduce."""
    checks = 0
    for start, ratio, threshold, deepest in CONFIGS:
        for j in range(deepest+1):
            for antithetic in (False, True):
                seed = SEEDS[0]+j
                seed_rng(seed)
                values, costs = rt.train_level(j, start, ratio, threshold, 5, antithetic)
                seed_rng(seed)
                for i in range(5):
                    same((values[i], costs[i]), pair_routine(antithetic)(j, start, ratio, threshold),
                         f"train_level{(j, start, ratio, threshold, antithetic)} row {i}")
                    checks += 1
    # The cheapest recorded plain and antithetic rows, rerun from their seeds.
    trained = [row for row in training['rows'] if row['levels']]
    for antithetic in (False, True):
        row = min((r for r in trained if r['config'].get('antithetic', False) == antithetic),
                  key=lambda r: sum(level['total_work'] for level in r['levels']))
        seed_rng(12000+row['index'])
        for level in row['levels']:
            values, costs = rt.train_level(level['level'], reps=level['n'], **row['config'])
            for key, actual in (('mean', values.mean()), ('second', (values*values).mean()),
                                ('work', costs.mean()), ('total_work', costs.sum())):
                require(abs(actual-level[key]) <= 1e-12*max(1.0, abs(level[key])),
                        f"training row {row['index']} level {level['level']} {key}: {actual} != recorded {level[key]}")
            checks += 1
    return checks


def expected_estimate(start, ratio, threshold, p, antithetic, sum_mode):
    """Two marked pilot terms, then one more fresh term than unmarked pilots."""
    cap = start*ratio**(len(p)-1)
    marked = unmarked = work = 0
    while marked < 2:
        _, cost = rt.real_term(start, ratio, threshold, p, antithetic, sum_mode)
        work += cost
        if uniform() < cost/cap:
            marked += 1
        else:
            unmarked += 1
    total = 0.0
    for _ in range(unmarked+1):
        value, cost = rt.real_term(start, ratio, threshold, p, antithetic, sum_mode)
        total += value
        work += cost
    return total/(unmarked+1), work


def check_estimates(selected):
    checks = 0
    for start, ratio, threshold, p in selected+[(16, 2, 1.0, np.array([.4, .3, .2, .1]))]:
        for antithetic, sum_mode in ((False, False), (True, False), (False, True)):
            what = f"real_estimate{(start, ratio, threshold, p.tolist(), antithetic, sum_mode)}"
            for seed in SEEDS[:25]:
                seed_rng(seed)
                actual = rt.real_estimate(start, ratio, threshold, p, antithetic, sum_mode)
                after = sentinels()
                seed_rng(seed)
                same(actual, expected_estimate(start, ratio, threshold, p, antithetic, sum_mode), f"{what} seed {seed}")
                require(sentinels() == after, f"{what} seed {seed}: unexpected extra draws")
                checks += 1
            for repeats in (1, 4):
                seed = SEEDS[0]+repeats
                seed_rng(seed)
                values, costs = rt.real_replicates(start, ratio, threshold, p, 2, antithetic, sum_mode, repeats)
                seed_rng(seed)
                for i in range(2):
                    runs = [rt.real_estimate(start, ratio, threshold, p, antithetic, sum_mode) for _ in range(repeats)]
                    same((values[i], costs[i]), (sum(v for v, _ in runs)/repeats, sum(c for _, c in runs)),
                         f"real_replicates repeats={repeats} seed {seed} row {i}")
                    checks += 1
    return checks


def check_levels(selection):
    checks = 0
    for budget in (16384, 65536):
        for start in (16, 64, 256, 1024):
            for ratio in (2, 4):
                levels = rt.level_count(budget, start, ratio)
                require(levels >= 1 and 4*start*ratio**(levels-1) <= budget < 4*start*ratio**levels,
                        f"level_count({budget}, {start}, {ratio}) = {levels} is not the largest fitting level")
                checks += 1
    selected = {}
    for row in selection['rows']:
        candidate = row['candidate']
        cfg, p = candidate['config'], np.array(candidate['probabilities'])
        levels = rt.level_count(row['budget']/cfg.get('repeats', 1), cfg['start'], cfg['ratio'])
        require(len(p) == levels and abs(p.sum()-1) < 1e-12 and np.all(p > 0),
                f"selected configuration at budget {row['budget']} has an invalid level law")
        # Both budgets selected the same law; replay each distinct one once.
        selected[(cfg['start'], cfg['ratio'], cfg['threshold'], tuple(p))] = p
        checks += 1
    return checks, [(start, ratio, threshold, p) for (start, ratio, threshold, _), p in selected.items()]


def load(name):
    path = ROOT/'results'/name
    require(path.is_file(), f"results/{name} is missing; run benchmark/run_real.py through 'lock' first")
    return json.loads(path.read_text())


def verify():
    selection, training, tuning = (load(name) for name in
                                   ('real_selection.json', 'real_training.json', 'real_tuning.json'))
    level_checks, selected = check_levels(selection)
    out = dict(passed=True, pair_replays=check_pairs(training), term_replays=check_terms(selected),
               tuning_cell_replays=check_tuning_cells(tuning), training_checks=check_training(training),
               estimate_replays=check_estimates(selected), level_checks=level_checks,
               selected_configurations=[[s, r, t, p.tolist()] for s, r, t, p in selected],
               scope='production routine replay against an independent scalar classifier; not a statistical error theorem')
    print(json.dumps(out))


if __name__ == '__main__':verify()
