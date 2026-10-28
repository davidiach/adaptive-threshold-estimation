import contextlib
import io
import math
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from threshold_toolkit.__main__ import main, read_rates
from threshold_toolkit.planner import (EvenlySpread, GuessedRates, _calls, _majority_plan,
                                       _odd_flip_counts, binomial_tail,
                                       difficulty, floor_budget, majority_plan_for_budget,
                                       majority_plan_for_target, plan_target, simulate)


def exact_positive_probability(p, cap):
    """P(the cap-N classifier says above 50/50 | p), by dynamic programming over checkpoints."""
    alive = {0: 1.0}  # successes so far -> probability, among unstopped paths
    positive = 0.0
    n = 0
    while alive:
        block = 1 if n == 0 else n
        grown = {}
        for s, w in alive.items():
            for j in range(block + 1):
                grown[s + j] = grown.get(s + j, 0.0) + w * math.comb(block, j) * p ** j * (1 - p) ** (block - j)
        n += block
        alive = {}
        for s, w in grown.items():
            margin = math.sqrt((1 + math.log(cap / n)) / n)
            if n >= cap or abs(s / n - 0.5) > margin:
                positive += w * (s / n > 0.5)
            else:
                alive[s] = w
    return positive


class BinomialTailTests(unittest.TestCase):
    def test_matches_exact_sums(self):
        rng = np.random.default_rng(0)
        p = np.concatenate([rng.random(15), [0.0, 1.0, 0.5, 1e-12, 1 - 1e-12]])
        for m in (1, 2, 3, 8, 31, 100, 255):
            for k in range(1, m + 1):
                exact = [sum(math.comb(m, j) * q ** j * (1 - q) ** (m - j) for j in range(k, m + 1))
                         for q in p]
                np.testing.assert_allclose(binomial_tail(m, k, p), exact, rtol=0, atol=1e-12)

    def test_large_counts_follow_the_normal_limit(self):
        m = 1_000_001
        tail = binomial_tail(m, (m + 1) // 2, np.array([0.5, 0.5 + 0.5 / math.sqrt(m)]))
        self.assertAlmostEqual(tail[0], 0.5, places=7)  # lgamma rounding at this size
        self.assertAlmostEqual(tail[1], 0.8413, places=3)

    def test_large_vector_converges_and_is_symmetric(self):
        m = 1_991_365
        p = (np.arange(4096) + 0.5) / 4096
        tail = binomial_tail(m, (m + 1) // 2, p)
        self.assertTrue(np.isfinite(tail).all())
        self.assertTrue((np.diff(tail) >= 0).all())
        np.testing.assert_allclose(tail + tail[::-1], 1, atol=1e-14)


class PopulationTests(unittest.TestCase):
    def test_fixed_gap_modulus(self):
        population = GuessedRates([0.7, 0.3])
        self.assertAlmostEqual(population.modulus(0.05), 0.25)
        self.assertEqual(population.modulus(0.3), 1.0)
        self.assertEqual(population.share_within(0.2), 1.0)
        self.assertEqual(population.true_fraction(), 0.5)

    def test_evenly_spread_matches_a_fine_grid(self):
        grid = GuessedRates((np.arange(200_000) + 0.5) / 200_000)
        spread = EvenlySpread()
        for h in (0.001, 0.05, 0.3, 0.6):
            self.assertAlmostEqual(spread.modulus(h), grid.modulus(h), places=4)
            self.assertAlmostEqual(spread.share_within(h), grid.share_within(h), places=4)

    def test_rates_must_be_probabilities(self):
        with self.assertRaises(ValueError):
            GuessedRates([0.5, 1.5])
        with self.assertRaises(ValueError):
            GuessedRates([])

    def test_zero_gaps_rejected(self):
        for rates in ([0.5], [0.5, 0.9], [0.5, 0.5, 0.1]):
            with self.subTest(rates=rates), self.assertRaisesRegex(ValueError, "positive-gap"):
                GuessedRates(rates)

    def test_uniform_majority_integral_matches_exact_formula(self):
        spread = EvenlySpread()
        for m in (1, 3, 7, 15, 101):
            a = (m + 1) // 2
            above, wrong = spread.majority_terms(m)
            self.assertEqual(above, 0.5)
            self.assertAlmostEqual(wrong, math.comb(2 * a, a) / 2 ** (2 * a + 1), places=14)
        # Wallis bounds independently detect the old midpoint-grid underestimate.
        m = 16_000_001
        a = (m + 1) / 2
        _, wrong = spread.majority_terms(m)
        self.assertGreater(wrong, 1 / (2 * math.sqrt(math.pi * (a + 0.5))))
        self.assertLess(wrong, 1 / (2 * math.sqrt(math.pi * a)))
        self.assertGreater(wrong, 0.0000997)


class FloorTests(unittest.TestCase):
    def test_floor_budget_inverts_the_floor(self):
        population = GuessedRates([0.9, 0.6, 0.52, 0.3])
        target = 0.002
        budget = floor_budget(population, target)
        self.assertLessEqual(difficulty(population, budget) / 64, target)
        self.assertGreater(difficulty(population, budget * 0.99) / 64, target)
        self.assertEqual(floor_budget(population, 0.1), 1.0)

    def test_finite_floor_beyond_old_search_cap(self):
        population = GuessedRates([0.5000000000000001, 0.1])
        budget = floor_budget(population, 0.005)
        self.assertTrue(math.isfinite(budget))
        self.assertGreater(budget, 1e30)
        self.assertLessEqual(difficulty(population, budget) / 64, 0.005 * (1 + 1e-14))
        self.assertGreater(difficulty(population, budget * 0.99) / 64, 0.005)


class MajorityPlanTests(unittest.TestCase):
    rates = [0.9, 0.7, 0.58, 0.53, 0.46, 0.2]

    def test_error_on_guess_matches_simulation(self):
        population = GuessedRates(self.rates)
        plan = majority_plan_for_budget(population, 5000)
        rng = np.random.default_rng(1)
        runs = 20_000
        rates = population.sample(rng, (runs, plan.items))
        above = rng.binomial(plan.flips_per_item, rates) > plan.flips_per_item / 2
        errors = above.mean(axis=1) - population.true_fraction()
        self.assertAlmostEqual(math.sqrt(np.mean(errors ** 2)), plan.error_on_guess, delta=0.003)

    def test_worst_case_covers_every_side(self):
        plan = majority_plan_for_budget(GuessedRates(self.rates), 5000)
        gaps = np.abs(np.array(self.rates) - 0.5)
        rng = np.random.default_rng(2)
        for _ in range(20):
            sides = rng.integers(0, 2, gaps.size) * 2 - 1
            moved = GuessedRates(0.5 + sides * gaps)
            m = plan.flips_per_item
            above = binomial_tail(m, (m + 1) // 2, moved.rates)
            error = math.sqrt((above.mean() - moved.true_fraction()) ** 2
                              + above.mean() * (1 - above.mean()) / plan.items)
            self.assertLessEqual(error, plan.worst_case_error + 1e-12)

    def test_target_plan_is_tight(self):
        population = GuessedRates(self.rates)
        plan = majority_plan_for_target(population, 0.04)
        self.assertLessEqual(plan.worst_case_error, 0.04)
        smaller = majority_plan_for_budget(population, plan.flips * 0.8)
        self.assertGreater(smaller.worst_case_error, 0.04)

    def test_unreachable_target(self):
        self.assertIsNone(majority_plan_for_target(GuessedRates([0.50001, 0.9]), 0.1,
                                                   max_flips_per_item=10_000))

    def test_budget_pruning_preserves_grid_optimum(self):
        for pop in (GuessedRates(self.rates), EvenlySpread()):
            budget = 5000
            exhaustive = min((_majority_plan(pop, m, budget // m)
                              for m in _odd_flip_counts(budget)), key=lambda p: p.worst_case_error)
            self.assertEqual(majority_plan_for_budget(pop, budget), exhaustive)

    def test_uniform_large_searches(self):
        plan = majority_plan_for_budget(EvenlySpread(), 3_000_000)
        self.assertLessEqual(plan.flips, 3_000_000)
        plan = majority_plan_for_target(EvenlySpread(), 0.0005)
        self.assertIsNotNone(plan)
        self.assertLessEqual(plan.worst_case_error, 0.0005)

    def test_invalid_targets_and_budgets(self):
        pop = GuessedRates(self.rates)
        for target in (math.inf, math.nan, 1e200, 0, -1, 1e-200):
            with self.subTest(target=target), self.assertRaises(ValueError):
                majority_plan_for_target(pop, target)
        for budget in (math.inf, math.nan, 0):
            with self.subTest(budget=budget), self.assertRaises(ValueError):
                majority_plan_for_budget(pop, budget)
            with self.subTest(simulation_budget=budget), self.assertRaises(ValueError):
                simulate(pop, budget, runs=2)
        with self.assertRaises(ValueError):
            plan_target(pop, 0.1, max_budget=math.inf)
        with self.assertRaises(ValueError):
            majority_plan_for_target(pop, 0.1, max_flips_per_item=math.inf)

    def test_loose_target_still_uses_at_least_one_item(self):
        plan = majority_plan_for_target(GuessedRates([0, 1]), 1)
        self.assertEqual(plan.items, 1)


class SimulationTests(unittest.TestCase):
    def test_calls_are_unbiased_for_the_capped_classifier(self):
        population = GuessedRates([0.85, 0.6, 0.52, 0.4])
        level_cap = 6
        exact = np.mean([exact_positive_probability(p, 2 ** level_cap) for p in population.rates])
        values, _ = _calls(population, level_cap, 1_000_000, np.random.default_rng(3))
        self.assertLess(abs(values.mean() - exact), 5 * values.std() / math.sqrt(values.size))

    def test_runs_respect_the_average_budget(self):
        population = GuessedRates([0.85, 0.6, 0.52, 0.4])
        sim = simulate(population, 256, runs=1000, seed=4)
        self.assertLess(sim.mean_flips, 256 * 1.1)
        self.assertGreater(sim.mean_flips, 256 * 0.7)
        self.assertLessEqual(sim.flips_p90, sim.flips_p99)


class CommandLineTests(unittest.TestCase):
    def run_cli(self, *args):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = main(list(args))
        return code, out.getvalue()

    def test_budget_report(self):
        code, text = self.run_cli("--rates", "0.9,0.6,0.55,0.3", "--budget", "2000", "--runs", "20")
        self.assertEqual(code, 0)
        self.assertIn("Simple plan:", text)
        self.assertIn("Proven no-tuning method", text)
        self.assertIn("no method can promise", text)

    def test_target_report(self):
        code, text = self.run_cli("--rates", "0.95,0.05", "--target-error", "0.1", "--runs", "20")
        self.assertEqual(code, 0)
        self.assertIn("meets the target however", text)
        self.assertIn("->", text)

    def test_zero_simulated_errors_do_not_divide_by_zero(self):
        for rates, budget in (("0,0.01", "4"), ("0", "100")):
            code, text = self.run_cli("--rates", rates, "--budget", budget, "--runs", "2")
            self.assertEqual(code, 0)
            self.assertIn("No error was observed", text)
            self.assertNotIn("infx", text)

    def test_target_plan_is_searched_once(self):
        with patch("threshold_toolkit.planner.majority_plan_for_target",
                   wraps=majority_plan_for_target) as search:
            code, _ = self.run_cli("--rates", "0.95,0.05", "--target-error", "0.1", "--runs", "2")
        self.assertEqual(code, 0)
        self.assertEqual(search.call_count, 1)

    def test_invalid_cli_inputs_are_reported_without_tracebacks(self):
        for args in (("--rates", "0.5", "--budget", "1000"),
                     ("--rates", "0.9,0.3", "--budget", "inf"),
                     ("--rates", "0.9,0.3", "--target-error", "inf"),
                     ("--rates", "0.9,0.3", "--target-error", "1e200")):
            with self.subTest(args=args), contextlib.redirect_stderr(io.StringIO()) as err:
                code, text = self.run_cli(*args)
                self.assertEqual(code, 2)
                self.assertIn("error:", err.getvalue())
                self.assertNotIn("no budget", text)

    def test_read_rates(self):
        self.assertEqual(read_rates("0.1, 0.2\n# note\n0.3 0.4;0.5"), [0.1, 0.2, 0.3, 0.4, 0.5])


if __name__ == "__main__":
    unittest.main()
