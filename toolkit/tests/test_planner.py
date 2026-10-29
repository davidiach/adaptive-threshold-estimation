import contextlib
import dataclasses
import io
import math
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from threshold_toolkit.__main__ import main, read_rates
from threshold_toolkit.planner import (EvenlySpread, GuessedRates, _calls, _confirmable_runs,
                                       _kl_upper_root, _majority_plan, _odd_flip_counts,
                                       _simulate_run, binomial_tail, difficulty, floor_budget,
                                       majority_plan_for_budget, majority_plan_for_target,
                                       plan_target, rms_upper_bound, simulate)


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

    def test_chunked_runs_keep_the_calibration(self):
        # Tiny chunks split both pilot streams and the production average.
        population = GuessedRates([0.85, 0.6, 0.52, 0.4])
        level_cap = 4
        exact = np.mean([exact_positive_probability(p, 2 ** level_cap) for p in population.rates])
        rng = np.random.default_rng(5)
        with patch("threshold_toolkit.planner.MAX_CHUNK", 8), \
                patch("threshold_toolkit.planner._calls", wraps=_calls) as calls:
            runs = np.array([_simulate_run(population, level_cap, rng) for _ in range(4000)])
        self.assertEqual(max(call.args[2] for call in calls.call_args_list), 8)
        raw, flips = runs[:, 0], runs[:, 1]
        self.assertLess(abs(raw.mean() - exact), 5 * raw.std() / math.sqrt(raw.size))
        # Expected total flips are exactly 4 * cap - (mean flips per call).
        _, costs = _calls(population, level_cap, 1_000_000, rng)
        expected = 4 * 2 ** level_cap - costs.mean()
        self.assertLess(abs(flips.mean() - expected), 5 * flips.std() / math.sqrt(flips.size))

    def test_budgets_too_large_to_simulate_are_rejected(self):
        population = GuessedRates([0.9, 0.3])
        for budget in (1e10, 1e300):
            with self.subTest(budget=budget), self.assertRaises(ValueError):
                simulate(population, budget, runs=2)
        # A generous cap is fine when the search stops long before it.
        self.assertLess(plan_target(population, 0.1, runs=2, max_budget=1e10).search_limit, 1e10)

    def test_target_search_can_finish_before_an_oversized_ceiling(self):
        # Every output is exactly zero, so the first trial's bound confirms this
        # target, and the search never reaches a budget too large to simulate.
        with patch("threshold_toolkit.planner.majority_plan_for_target", return_value=None):
            plan = plan_target(GuessedRates([0.0]), 0.2, max_budget=1e10)
        self.assertEqual(plan.search_limit, 1e10)
        self.assertEqual([trial.budget for trial in plan.trials], [4])
        self.assertEqual(plan.recommended.rms_error, 0.0)
        self.assertEqual(plan.recommended.runs, 200)

    def test_target_search_rejects_only_the_first_oversized_trial(self):
        trials = []
        # This seeded population does not meet the target at either allowed
        # budget. A small limit tests the failure without expensive simulations.
        with patch("threshold_toolkit.planner.MAX_SIMULATED_BUDGET", 8):
            with self.assertRaisesRegex(ValueError, "too large to simulate"):
                plan_target(GuessedRates([1.0]), 1e-5, runs=2,
                            max_budget=16, progress=trials.append)
        self.assertEqual([trial.budget for trial in trials], [4, 8])


class ConfidenceBoundTests(unittest.TestCase):
    def test_zero_observed_errors_leave_uncertainty(self):
        # 200 zero errors: 95% bound sqrt(1 - 0.05**(1/200)), about 0.122.
        exact = math.sqrt(-math.expm1(math.log(0.05) / 200))
        bound = rms_upper_bound(np.zeros(200), 0.95)
        self.assertGreaterEqual(bound, exact)
        self.assertAlmostEqual(bound, exact, places=9)

    def test_bound_covers_the_true_rms_error(self):
        rng = np.random.default_rng(11)
        for p in (0.001, 0.05, 0.3):
            losses = rng.random((2000, 200)) < p
            covered = np.mean([rms_upper_bound(row, 0.95) >= math.sqrt(p) for row in losses])
            with self.subTest(p=p):
                self.assertGreaterEqual(covered, 0.93)
        mixed = rng.random(500) ** 3
        self.assertGreater(rms_upper_bound(mixed), math.sqrt(mixed.mean()))

    def test_invalid_inputs_rejected(self):
        for losses, confidence in (([], 0.95), ([0.1, 1.5], 0.95), ([-0.1], 0.95),
                                   ([0.1], 0.0), ([0.1], 1.0), ([math.nan], 0.95)):
            with self.subTest(losses=losses, confidence=confidence), self.assertRaises(ValueError):
                rms_upper_bound(losses, confidence)

    def test_external_review_witness_is_not_recommended(self):
        # Exact RMS error at budget 4 is sqrt(0.01 * (1 - 1/sqrt(2))) = 0.0541, but all 200
        # simulated errors are zero with probability 0.556. The old search recommended it.
        plan = plan_target(GuessedRates([0.01]), 0.001, runs=200, seed=0, max_budget=64)
        self.assertIsNone(plan.recommended)
        hit = plan.first_simulated_hit
        self.assertEqual((hit.budget, hit.rms_error), (4, 0.0))
        self.assertGreater(hit.rms_error_upper, 0.122)
        # 200 runs can never confirm 0.001, so the search stops at the first hit.
        self.assertGreater(plan.confirmable_runs, 1_000_000)
        self.assertEqual([trial.budget for trial in plan.trials], [4])

    def test_tiny_targets_and_oversized_ceilings_do_not_fail(self):
        plan = plan_target(GuessedRates([0.0]), 1e-150, runs=2, max_budget=8)
        self.assertGreater(plan.confirmable_runs, 10 ** 15)
        self.assertIsNone(plan.recommended)
        # From a review: this target's square is the smallest subnormal, but
        # the margined square underflowed to zero and the count divided by it.
        plan = plan_target(GuessedRates([0.5000001]), 1.5717277847026288e-162, runs=2, max_budget=8)
        self.assertEqual(plan.confirmable_runs, sys.maxsize)
        self.assertIsNone(plan.recommended)
        # With enough runs to continue past an unconfirmed hit, the search stops
        # at the simulation limit and keeps that hit instead of raising.
        real = simulate(GuessedRates([0.9, 0.2]), 4, runs=2, seed=0)
        hit = dataclasses.replace(real, rms_error=0.1, rms_error_upper=0.5)
        with patch("threshold_toolkit.planner.MAX_SIMULATED_BUDGET", 8), \
                patch("threshold_toolkit.planner.simulate", side_effect=lambda *a, **k: hit):
            plan = plan_target(GuessedRates([0.9, 0.2]), 0.3, runs=1000, max_budget=64)
        self.assertEqual(len(plan.trials), 2)
        self.assertIs(plan.first_simulated_hit, hit)
        self.assertIsNone(plan.recommended)

    def test_search_continues_past_an_unconfirmed_hit_when_runs_suffice(self):
        real = simulate(GuessedRates([0.9, 0.2]), 4, runs=2, seed=0)
        fake = iter([dataclasses.replace(real, rms_error=0.1, rms_error_upper=0.5),
                     dataclasses.replace(real, rms_error=0.05, rms_error_upper=0.25)])
        with patch("threshold_toolkit.planner.simulate", side_effect=lambda *a, **k: next(fake)) as sim:
            plan = plan_target(GuessedRates([0.9, 0.2]), 0.3, runs=1000, max_budget=64)
        self.assertLessEqual(plan.confirmable_runs, 1000)
        self.assertEqual(plan.first_simulated_hit.rms_error_upper, 0.5)
        self.assertEqual(plan.recommended.rms_error_upper, 0.25)
        # Each trial's bound is corrected for the five budgets 4, ..., 64.
        self.assertEqual(sim.call_args.kwargs["confidence"], 0.95)
        self.assertEqual(sim.call_args.kwargs["comparisons"], 5)

    def test_comparisons_share_the_error_probability(self):
        # Five bounds at 95% overall: each holds with probability 0.99.
        exact = math.sqrt(-math.expm1(math.log(0.01) / 200))
        bound = rms_upper_bound(np.zeros(200), 0.95, comparisons=5)
        self.assertGreaterEqual(bound, exact)
        self.assertAlmostEqual(bound, exact, places=9)
        for comparisons in (0, 1.5):
            with self.subTest(comparisons=comparisons), self.assertRaises(ValueError):
                rms_upper_bound([0.1], 0.95, comparisons=comparisons)

    def test_confirmable_runs_match_the_zero_error_bound(self):
        # From a review: the count ignored the bound's relative margin, so for
        # this target 200 error-free runs could not confirm it.
        target = 0.16667562365558541
        plan = plan_target(GuessedRates([0.9, 0.6, 0.52, 0.3]), target, runs=2)
        self.assertEqual(plan.confirmable_runs, 201)
        # Further review witnesses: targets within rounding of a count boundary,
        # and a tiny target at low confidence, where the old relative entropy
        # lost precision and the closed form was 89 runs too many.
        rng = np.random.default_rng(5)
        cases = ([(target, 0.95, 14), (0.45367021678547953, 0.95, 1),
                  (0.5087883168969028, 0.95, 1), (0.03, 0.95, 22), (1e-6, 1e-6, 1)]
                 + [(t, 0.95, k) for t in rng.uniform(0.05, 0.9, 40) for k in (1, 5, 22)])
        for t, confidence, k in cases:
            n = _confirmable_runs(t, confidence, k)
            with self.subTest(target=t, confidence=confidence, comparisons=k):
                self.assertLessEqual(rms_upper_bound(np.zeros(n), confidence, k), t)
                if n > 1:
                    self.assertGreater(rms_upper_bound(np.zeros(n - 1), confidence, k), t)
        self.assertEqual(_confirmable_runs(0.03, 0.95, 22), 6761)

    def test_run_count_search_ends_when_the_allowance_is_subnormal(self):
        # From a review: with K = 1 and an absurdly small confidence,
        # log(1 / delta) / n is subnormal and the bound moves in coarse steps.
        # Stepping one run at a time from the closed form took years, or never
        # ended when no count could meet the target.
        self.assertEqual(_confirmable_runs(2e-162, 1e-310, 1), sys.maxsize)
        # Near 2**63 the closed form rounds past sys.maxsize although a count
        # 511 runs below it already meets the target.
        self.assertEqual(_confirmable_runs(5.699104706590443e-10, 0.95, 1), sys.maxsize - 511)
        for target, confidence in ((1e-160, 1e-302), (1e-155, 1e-292)):
            n = _confirmable_runs(target, confidence, 1)
            allowance = -math.log1p(-confidence)
            with self.subTest(target=target):
                self.assertLess(n, sys.maxsize)
                self.assertLessEqual(_kl_upper_root(0.0, allowance / n), target)
                self.assertGreater(_kl_upper_root(0.0, allowance / (n - 1)), target)

    def test_subnormal_mean_errors_keep_the_zero_error_bound(self):
        # From a review: (q - p) / p overflowed for a subnormal mean p, the
        # relative entropy became -inf, and the bound jumped to 1.
        zero = rms_upper_bound(np.zeros(200), 0.95)
        for mean in (1e-310, 5e-324):
            with self.subTest(mean=mean):
                self.assertAlmostEqual(rms_upper_bound(np.full(200, mean), 0.95), zero, places=12)

    def test_extreme_confidence_levels_are_planned(self):
        # From a review: 1 - (1 - confidence) / K rounded to 1 or 0, so simulate
        # rejected these valid levels as outside (0, 1).
        population = GuessedRates([0.3, 0.7])
        for confidence, max_budget in ((1 - 2e-16, 4 * 2 ** 22), (1e-20, 4)):
            with self.subTest(confidence=confidence):
                plan = plan_target(population, 0.5, runs=20, max_budget=max_budget,
                                   confidence=confidence)
                self.assertTrue(plan.trials)
                self.assertTrue(all(0 < t.rms_error_upper <= 1 for t in plan.trials))


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

    def test_unconfirmed_target_is_not_reported_as_met(self):
        code, text = self.run_cli("--rates", "0.01", "--target-error", "0.001", "--max-budget", "64")
        self.assertEqual(code, 0)
        self.assertIn("do not confirm it", text)
        self.assertIn("needs at least", text)
        self.assertNotIn("confirmed at", text)

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
                     ("--rates", "0.9,0.3", "--target-error", "1e200"),
                     ("--rates", "0.9,0.3", "--budget", "1e300")):
            with self.subTest(args=args), contextlib.redirect_stderr(io.StringIO()) as err:
                code, text = self.run_cli(*args)
                self.assertEqual(code, 2)
                self.assertIn("error:", err.getvalue())
                self.assertNotIn("no budget", text)

    def test_high_confidence_is_never_shown_as_certain(self):
        # From a review: six significant digits printed 0.9999999 as "100%".
        for mode, confidence, shown in ((("--budget", "2000"), "0.9999999", "99.99999%"),
                                        (("--target-error", "0.5"), "0.9999999999999999",
                                         "99.99999999999999%")):
            with self.subTest(mode=mode):
                code, text = self.run_cli("--rates", "0.3,0.7", *mode, "--runs", "20",
                                          "--confidence", confidence)
                self.assertEqual(code, 0)
                self.assertIn(f"{shown} confidence", text)
                self.assertNotIn("100% confidence", text)

    def test_search_stopped_at_the_simulation_limit_is_reported(self):
        real = simulate(GuessedRates([0.9, 0.2]), 4, runs=2, seed=0)
        hit = dataclasses.replace(real, rms_error=0.1, rms_error_upper=0.5)
        with patch("threshold_toolkit.planner.MAX_SIMULATED_BUDGET", 8), \
                patch("threshold_toolkit.__main__.MAX_SIMULATED_BUDGET", 8), \
                patch("threshold_toolkit.planner.simulate",
                      side_effect=lambda _, budget, *a, **k: dataclasses.replace(hit, budget=budget)):
            code, text = self.run_cli("--rates", "0.9,0.2", "--target-error", "0.3",
                                      "--runs", "1000", "--max-budget", "64")
        self.assertEqual(code, 0)
        self.assertIn("No budget up to 8 flips was confirmed", text)
        self.assertIn("Budgets above 8 flips are too large to simulate", text)
        self.assertNotIn("up to 64 flips", text)

    def test_whole_percentages_are_not_written_as_exponents(self):
        code, text = self.run_cli("--rates", "0.95,0.05", "--target-error", "1", "--runs", "2")
        self.assertEqual(code, 0)
        self.assertIn("about 100 percentage points", text)
        self.assertNotIn("e+02", text)

    def test_read_rates(self):
        self.assertEqual(read_rates("0.1, 0.2\n# note\n0.3 0.4;0.5"), [0.1, 0.2, 0.3, 0.4, 0.5])


if __name__ == "__main__":
    unittest.main()
