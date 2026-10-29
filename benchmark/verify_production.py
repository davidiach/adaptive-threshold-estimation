"""Replay checks of the production direct-real routines.

verify_real.py, locked in results/real_selection.json, checks tape_pair,
antithetic_tape and sum_tape: copies of the stopping state machines run on
prescribed tapes. This script checks the routines that produced the training,
tuning and held-out results. It reseeds Numba's generator, replays the exact
draws each routine makes, and compares every value and cost with an
independent scalar classifier on the replayed tape:

- real_pair, antithetic_pair and sum_term, including the selected
  start-1024, ratio-4 randomized sums;
- real_term's level draw and 1/p_J weighting in all three modes;
- real_estimate's two-success calibration and real_replicates' repeats;
- level_count, and the level count of every selected configuration.

These are implementation checks, not statistical error guarantees.
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


@njit
def uniform():
    return np.random.random()


@njit
def normal():
    return np.random.normal()


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


def check_pairs():
    checks = 0
    for start, ratio, threshold, deepest in CONFIGS:
        for j in range(deepest+1):
            for antithetic in (False, True):
                pair = rt.antithetic_pair if antithetic else rt.real_pair
                for seed in SEEDS:
                    seed_rng(seed)
                    actual = pair(j, start, ratio, threshold)
                    seed_rng(seed)
                    xs = observations(normal(), start*ratio**j)
                    same(actual, expected_pair(xs, j, start, ratio, threshold, antithetic),
                         f"{pair.__name__}{(j, start, ratio, threshold)} seed {seed}")
                    checks += 1
    return checks


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
                seed_rng(seed)
                actual = rt.real_term(start, ratio, threshold, p, antithetic, sum_mode)
                same(actual, replay_term(seed, start, ratio, threshold, p, antithetic, sum_mode),
                     f"real_term{(start, ratio, threshold, p.tolist(), antithetic, sum_mode)} seed {seed}")
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
            for seed in SEEDS[:25]:
                seed_rng(seed)
                actual = rt.real_estimate(start, ratio, threshold, p, antithetic, sum_mode)
                seed_rng(seed)
                same(actual, expected_estimate(start, ratio, threshold, p, antithetic, sum_mode),
                     f"real_estimate{(start, ratio, threshold, p.tolist(), antithetic, sum_mode)} seed {seed}")
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


def verify():
    selection = json.loads((ROOT/'results/real_selection.json').read_text())
    level_checks, selected = check_levels(selection)
    out = dict(passed=True, pair_replays=check_pairs(), term_replays=check_terms(selected),
               estimate_replays=check_estimates(selected), level_checks=level_checks,
               selected_configurations=[[s, r, t, p.tolist()] for s, r, t, p in selected],
               scope='production routine replay against an independent scalar classifier; not a statistical error theorem')
    print(json.dumps(out))


if __name__ == '__main__':verify()
