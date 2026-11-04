"""Executable-controller tests, including a continuous-law oracle independent of the finite adapter."""

from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
from random import Random
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from threshold_toolkit.confidence_amplification import MedianSchedule, run_capped_median
from threshold_toolkit.known_law_oracle import FiniteGapOracle, SplitIntegrals
from threshold_toolkit.known_rare_estimator import (
    Level,
    RarePlan,
    _classify,
    _ordinary_stop,
    estimate_known_rare,
    known_rare_program,
    plan_known_rare,
)
from threshold_toolkit.rare_event_functional import FiniteGapLaw, Interval


class UniformUpperBand:
    """Uniform d on (1/4,1/2). These conservative integrals suffice for B >= 16."""

    def split(self, rho, budget, precision):
        assert budget >= 16
        t = (1 + rho) / 4
        return SplitIntegrals(
            {0: 4 * (1 / t - 2)},
            F(0),
            4 * rho,
            lambda m: min(F(1), F(16, m) ** 2),
            lambda m: rho * m,
        )

    def null_prefix(self, heads, tails, tolerance):
        # Under the all-negative law, p is uniform on (0,1/4).
        d = sum(
            (-1) ** k * comb(tails, k) * F(1, 4 ** (heads + k) * (heads + k + 1))
            for k in range(tails + 1)
        )
        return Interval(d, d)


def classify(plan, level, tape):
    program = _classify(plan, level, 0)
    item = next(program)
    used = 0
    while True:
        assert item == 0
        bit = next(tape)
        used += 1
        try:
            item = program.send(bit)
        except StopIteration as stop:
            return stop.value, used


class RareEstimatorTests(unittest.TestCase):
    def setUp(self):
        self.law = FiniteGapOracle(FiniteGapLaw([("1/2", 1)]))

    def test_constant_requires_no_coins(self):
        plan = plan_known_rare(self.law, rho="1/4", budget=1)
        out = estimate_known_rare(lambda: self.fail("constant requested a coin"), plan)
        self.assertEqual(
            (out.value, out.items, out.flips, plan.mse_bound), (F(1, 8), 0, 0, F(1, 64))
        )

    def test_budget_and_mse_accounting(self):
        for law in (self.law, UniformUpperBand()):
            p = plan_known_rare(law, rho="1/4", budget=10**6)
            self.assertGreater(len(p.levels), 1)
            self.assertEqual(
                sum(level.mean_count * level.mark_work for level in p.levels), p.budget
            )
            self.assertEqual(
                p.mse_bound,
                p.levels[-1].error ** 2
                + sum(17 * level.error / level.mean_count for level in p.levels),
            )
            self.assertLess(p.mse_bound, (p.rho / 2) ** 2)

    def test_continuous_null_integral(self):
        u = UniformUpperBand()
        self.assertEqual(u.null_prefix(1, 1, F(1, 100)).upper, F(1, 8) - F(1, 48))

    def test_zero_null_and_charged_flips(self):
        p = plan_known_rare(self.law, rho="1/4", budget=65536)
        data = iter((1, 0))
        self.assertEqual(classify(p, p.levels[0], data), (1, 2))
        with self.assertRaises(StopIteration):
            next(data)

    def test_adjacent_levels_reuse_one_item_and_fresh_flips(self):
        tape = iter([iter([0, 0]), iter([1, 1, 0, 0])])
        p = RarePlan(
            self.law,
            F(1, 4),
            F(100),
            ((0, F(1)),),
            (Level(1, F(1, 64), F(2), F(1)), Level(1, F(1, 1024), F(4), F(1))),
            F(1),
        )
        result = estimate_known_rare(lambda: next(tape).__next__, p, rng=Random(14))
        self.assertEqual((result.items, result.flips, result.value), (2, 6, F(1, 4)))

    def test_cap_and_negative_majority_ties_by_exhaustion(self):
        law = FiniteGapOracle(FiniteGapLaw([("1/4", 1)]))
        level = Level(4, F(1, 1024), F(8), F(1))
        plan = RarePlan(law, F(1, 4), F(8), ((1, F(1)),), (level,), F(1))
        for path in product((0, 1), repeat=8):
            tape = iter(path)
            actual = classify(plan, level, tape)
            self.assertEqual(actual, (int(sum(path[1::2]) > 2), 8))

    def test_normal_entry_point_with_physical_accounting(self):
        population, private = Random(21), Random(17)
        seen = [0, 0]

        def new_item():
            seen[0] += 1
            bit = int(population.randrange(8) == 0)

            def flip():
                seen[1] += 1
                return bit

            return flip

        plan = plan_known_rare(self.law, rho="1/4", budget=65536)
        result = estimate_known_rare(new_item, plan, rng=private)
        self.assertEqual(seen, [result.items, result.flips])
        self.assertGreaterEqual(result.value, 0)
        self.assertLessEqual(result.value, plan.rho)

    def test_known_law_under_physical_cap(self):
        schedule = MedianSchedule(19 * 8 * 65536, rho="1/4", delta="1/4")
        plan = plan_known_rare(
            self.law, rho=schedule.rho, budget=schedule.base_expected_budget
        )
        self.assertTrue(plan.levels)
        flips = 0

        def factory(rng):
            bit = int(rng.randrange(8) == 0)

            def flip():
                nonlocal flips
                flips += 1
                return bit

            return flip

        def program(budget, rng):
            self.assertEqual(budget, plan.budget)
            return known_rare_program(plan, rng)

        result = run_capped_median(schedule, program, factory, seed=12)
        self.assertEqual(flips, result.flips)
        self.assertGreater(flips, 0)
        self.assertLessEqual(flips, schedule.total_budget)
        self.assertTrue(
            all(n <= schedule.per_block_cap for n in result.per_block_flips)
        )

    def test_timeout_between_paired_flips(self):
        from threshold_toolkit.confidence_amplification import _run_block

        level = Level(1, F(1, 64), F(2), F(1))
        plan = RarePlan(self.law, F(1, 4), F(2), ((0, F(1)),), (level,), F(1))
        for cap, expected in [(1, (F(1, 8), 1, 1, True)), (2, (F(1, 4), 2, 1, False))]:
            program = known_rare_program(plan, Random(0))
            result = _run_block(
                program, lambda rng: lambda: 1, Random(0), cap, plan.rho
            )
            self.assertEqual(result, expected)

    def test_fractional_allocation_counts(self):
        level = Level(1, F(1, 64), F(2), F(1, 3))
        plan = RarePlan(self.law, F(1, 4), F(2, 3), ((0, F(1)),), (level,), F(1))

        class Draw:
            def __init__(self, k):
                self.k = k

            def randrange(self, n):
                assert n == 3
                return self.k

        flips = [
            estimate_known_rare(lambda: lambda: 1, plan, rng=Draw(i)).flips
            for i in range(3)
        ]
        self.assertEqual(flips, [2, 0, 0])

    def test_ordinary_threshold_and_oracle_width(self):
        self.assertFalse(_ordinary_stop(4, 4, 16))
        self.assertTrue(_ordinary_stop(16, 16, 64))

        class Wide(UniformUpperBand):
            def null_prefix(self, heads, tails, tolerance):
                return Interval(F(0), F(1))

        p = plan_known_rare(Wide(), rho="1/4", budget=10**6)
        with self.assertRaisesRegex(ValueError, "enclosure contract"):
            classify(p, p.levels[0], iter((1, 1)))
