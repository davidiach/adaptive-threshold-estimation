import itertools
import math
import random
import subprocess
import sys
import unittest
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from threshold_toolkit.estimator import (block_flipper, budget_level, coupled_call,
                                         estimate_fraction, level_probability,
                                         majority_vote_estimate, sample_level,
                                         two_success_average)
from threshold_toolkit.planner import score_blocks


def reference_classifier(bits, cap):
    """The capped classifier written directly from the paper's definition."""
    n = 1
    while True:
        mean = sum(bits[:n]) / n
        if n >= cap or abs(mean - 0.5) > math.sqrt((1 + math.log(cap / n)) / n):
            return int(mean > 0.5), n
        n *= 2


def tape_flipper(bits):
    """A scripted item: each flip reads the next bit; records how many were read."""
    position = [0]

    def flip():
        position[0] += 1
        return bits[position[0] - 1]
    return flip, position


def block_counts(bits, level):
    """Successes in blocks 0->1->2->4->...->2^level of a tape."""
    edges = [0] + [2 ** k for k in range(level + 1)]
    return [sum(bits[edges[i]:edges[i + 1]]) for i in range(level + 1)]


class BudgetTests(unittest.TestCase):
    def test_budget_level(self):
        self.assertEqual(budget_level(4), 0)
        self.assertEqual(budget_level(7.99), 0)
        self.assertEqual(budget_level(8), 1)
        self.assertEqual(budget_level(65536), 14)
        self.assertEqual(budget_level(65535), 13)
        with self.assertRaises(ValueError):
            budget_level(3.9)

    def test_nonfinite_budgets_rejected(self):
        for budget in (math.inf, -math.inf, math.nan):
            with self.subTest(budget=budget), self.assertRaises(ValueError):
                estimate_fraction(lambda: (lambda: True), budget)

    def test_execution_api_imports_without_numerical_dependencies(self):
        root = str(Path(__file__).resolve().parents[1])
        script = (f"import sys; sys.path.insert(0, {root!r}); "
                  "from threshold_toolkit import estimate_fraction; "
                  "assert 'numpy' not in sys.modules and 'scipy' not in sys.modules; "
                  "assert estimate_fraction(lambda: (lambda: False), 4, seed=0).estimate == 0")
        subprocess.run([sys.executable, "-S", "-c", script], check=True, timeout=10)

    def test_level_law(self):
        rng = random.Random(1)
        draws = [sample_level(rng) for _ in range(200_000)]
        for level in range(8):
            p = level_probability(level)
            freq = draws.count(level) / len(draws)
            self.assertLess(abs(freq - p), 5 * math.sqrt(p * (1 - p) / len(draws)))


class CallTests(unittest.TestCase):
    def test_call_matches_reference_and_simulator_on_random_tapes(self):
        rng = random.Random(2)
        for _ in range(3000):
            level = rng.randrange(0, 9)
            p = rng.random()
            bits = [int(rng.random() < p) for _ in range(2 ** level)]
            fine, stop = reference_classifier(bits, 2 ** level)
            coarse = reference_classifier(bits, 2 ** (level - 1))[0] if level else 0
            expected = (fine - coarse) / level_probability(level)

            flip, position = tape_flipper(bits)
            value, cost = coupled_call(block_flipper(flip, False), level)
            self.assertEqual((value, cost), (expected, stop))
            self.assertEqual(position[0], cost, "a call must read only the flips it charges")

            values, costs = score_blocks(np.array([block_counts(bits, level)]), level)
            self.assertEqual((values[0], costs[0]), (expected, stop))

    def test_levels_telescope_exactly(self):
        # Summing p_l * E[call value at level l] over l <= L gives P(Z_N = 1) exactly.
        level_cap = 3
        cap = 2 ** level_cap
        for p in (0.37, 0.5, 0.61, 0.9):
            telescoped = 0.0
            positive = 0.0
            for bits in itertools.product((0, 1), repeat=cap):
                weight = p ** sum(bits) * (1 - p) ** (cap - sum(bits))
                positive += weight * reference_classifier(bits, cap)[0]
                for level in range(level_cap + 1):
                    flip, _ = tape_flipper(bits)
                    value, _ = coupled_call(block_flipper(flip, False), level)
                    telescoped += weight * level_probability(level) * value
            self.assertAlmostEqual(telescoped, positive, places=12)


class CalibrationTests(unittest.TestCase):
    def test_two_success_identities(self):
        # Cost uniform on {1,...,9}, value correlated with cost: mean 5, variance 7.
        rng = random.Random(3)

        def run_once():
            cost = rng.randrange(9) + 1
            return cost + rng.uniform(-1, 1), cost

        cap, mean_cost, mean_value, variance = 9, 5.0, 5.0, 7.0
        reps = 40_000
        results = [two_success_average(run_once, cap, rng) for _ in range(reps)]
        averages = np.array([r[0] for r in results])
        costs = np.array([r[1] for r in results])
        self.assertLess(abs(averages.mean() - mean_value), 5 * averages.std() / math.sqrt(reps))
        self.assertLess(abs(averages.var() / (variance * mean_cost / cap) - 1), 0.05)
        self.assertLess(abs(costs.mean() - (4 * cap - mean_cost)), 5 * costs.std() / math.sqrt(reps))

    def test_cost_outside_cap_rejected(self):
        with self.assertRaises(ValueError):
            two_success_average(lambda: (0.0, 9), 8, random.Random(0))

    def test_zero_cost_and_invalid_caps_rejected(self):
        for cost in (0, -1, math.inf, math.nan):
            with self.subTest(cost=cost), self.assertRaises(ValueError):
                two_success_average(lambda: (1.0, cost), 8, random.Random(0))
        for cap in (0, -1, math.inf, math.nan):
            with self.subTest(cap=cap), self.assertRaises(ValueError):
                two_success_average(lambda: (1.0, 1), cap, random.Random(0))


class Population:
    """Items with fixed success rates, each flipping from its own seeded stream."""

    def __init__(self, rates, seed, batched):
        self.rates = rates
        self.picker = random.Random(seed)
        self.batched = batched
        self.created = 0
        self.flips = 0

    def new_item(self):
        rate = self.picker.choice(self.rates)
        stream = random.Random(self.picker.getrandbits(64))
        self.created += 1

        def flip_once():
            self.flips += 1
            return stream.random() < rate

        if self.batched:
            return lambda k: sum(flip_once() for _ in range(k))
        return flip_once


class EstimateFractionTests(unittest.TestCase):
    rates = [0.9, 0.7, 0.55, 0.45, 0.2]

    def test_batched_and_single_flips_agree_and_accounting_is_exact(self):
        for seed in range(20):
            results = []
            for batched in (False, True):
                population = Population(self.rates, seed, batched)
                result = estimate_fraction(population.new_item, 300, batched=batched, seed=seed)
                self.assertEqual(result.flips, population.flips)
                self.assertEqual(result.items, population.created)
                self.assertTrue(0 <= result.estimate <= 1)
                self.assertEqual(result.cap, 64)
                results.append(result)
            self.assertEqual(results[0], results[1])

    def test_average_flips_stay_within_budget(self):
        flips = np.array([
            estimate_fraction(Population(self.rates, seed, True).new_item, 64,
                              batched=True, seed=seed).flips
            for seed in range(2000)])
        # Expected flips are exactly 4N - c <= 64 here.
        self.assertLess(flips.mean(), 64 + 5 * flips.std() / math.sqrt(flips.size))

    def test_bad_flips_rejected(self):
        with self.assertRaises(ValueError):
            estimate_fraction(lambda: (lambda: 2), 16, seed=0)
        with self.assertRaises(ValueError):
            estimate_fraction(lambda: (lambda k: k + 1), 16, batched=True, seed=0)


class MajorityVoteTests(unittest.TestCase):
    def test_deterministic_items(self):
        picker = random.Random(4)

        def new_item():
            sure = picker.random() < 0.3
            return lambda: sure

        self.assertAlmostEqual(majority_vote_estimate(new_item, 10_000, 3), 0.3, delta=0.02)

    def test_batched_matches_single(self):
        shares = []
        for batched in (False, True):
            population = Population([0.8, 0.2, 0.6], 5, batched)
            shares.append(majority_vote_estimate(population.new_item, 50, 7, batched=batched))
            self.assertEqual(population.flips, 350)
        self.assertEqual(shares[0], shares[1])

    def test_even_flips_rejected(self):
        with self.assertRaises(ValueError):
            majority_vote_estimate(lambda: (lambda: True), 10, 4)


if __name__ == "__main__":
    unittest.main()
