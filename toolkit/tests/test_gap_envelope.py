"""Finite exact checks of the learned-law construction and paid controllers."""

from dataclasses import replace
from fractions import Fraction as F
from math import comb
from pathlib import Path
from random import Random
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from threshold_toolkit.arbitrary_law_confidence import arbitrary_law_confidence, arbitrary_law_interval
from threshold_toolkit.budget_ladders import _execute
from threshold_toolkit.confidence_ladders import ClosedInterval
from threshold_toolkit.gap_envelope import (
    GapEnvelope, _probe_program, gap_envelope_program, plan_gap_envelope, run_gap_envelope,
)
from threshold_toolkit.known_law_confidence import known_law_interval
from threshold_toolkit.known_rare_estimator import RarePlan, _ordinary_stop, plan_known_rare
from threshold_toolkit.rare_event_functional import Precision, cost_entropy
from threshold_toolkit.tail_mass import TailMassProbe


class GapEnvelopeTests(unittest.TestCase):
    def test_exact_budget_allocation_and_sample_cap(self):
        for depth in range(1, 18):
            for rho in [F(1, 4), F(1, 1000)]:
                plan = plan_gap_envelope(depth, rho=rho, delta=F(1, 20))
                n = 4**depth
                self.assertLessEqual(sum(plan.probe_caps), n)
                self.assertGreaterEqual(sum(plan.probe_caps), n // 2)
                self.assertGreaterEqual(plan.coin_cap**2 * rho, 64 * n)
                self.assertLess((plan.coin_cap - 1)**2 * rho, 64 * n)
                exponent = (plan.blocks - 1) // 8
                self.assertLessEqual(F(2 * depth, 2**exponent), plan.delta)
                for j, cap in enumerate(plan.probe_caps, 1):
                    self.assertGreaterEqual(cap, F(n, 2 * j * (j + 1)))
                    self.assertGreaterEqual(cap, 2**(depth + j - 2))

    def test_generator_matches_original_probe_at_every_paid_prefix(self):
        def make_factory():
            counts = []

            def factory(rng):
                i = len(counts)
                counts.append(0)

                def flip():
                    prefix = counts[i]
                    counts[i] += 1
                    return i % 2 if i < 2 else prefix % 2

                return flip

            return factory, counts

        for cap in range(401):
            first, counts_a = make_factory()
            second, counts_b = make_factory()
            old = TailMassProbe(4, first).advance_to(cap)
            value, used, made, timed_out = _execute(_probe_program(4, cap, 10000), second, Random(0), cap)
            self.assertFalse(timed_out)
            self.assertEqual((value, used, made), (old.upper, old.flips, old.items))
            self.assertEqual(counts_a, counts_b)

    def test_completed_coin_cap_stops_before_creating_another_coin(self):
        counts = [0, 0]

        def factory(rng):
            counts[0] += 1

            def flip():
                counts[1] += 1
                return 0

            return flip

        value, used, made, timeout = _execute(_probe_program(4, 10000, 16), factory, Random(0), 10000)
        self.assertFalse(timeout)
        self.assertEqual(value, F(1, 2))
        self.assertEqual((made, used), (16, 1024))
        self.assertEqual(counts, [16, 1024])

    def test_cdf_rounding_is_conservative_including_boundary_atoms(self):
        actual = [(F(1, 16), F(1, 10)), (F(1, 8), F(1, 5)),
                  (F(3, 16), F(1, 5)), (F(1, 2), F(1, 2))]
        bounds = [sum(w for d, w in actual if d <= F(1, 2**j)) for j in range(1, 5)]
        law = GapEnvelope(bounds)
        self.assertEqual(sum(w for _, w in law.atoms) + law.zero_mass, 1)
        for k in range(129):
            x = F(k, 256)
            truth = sum(w for d, w in actual if d <= x)
            envelope = law.zero_mass + sum(w for d, w in law.atoms if d <= x)
            self.assertGreaterEqual(envelope, truth)

    def test_zero_atom_and_split_boundary_accounting(self):
        law = GapEnvelope([1, F(1, 2), F(1, 10)])
        split = law.split(F(1, 4), F(1000), Precision())
        self.assertEqual(split.band_costs, {1: F(8), 2: F(16)})
        self.assertEqual(split.unresolved_mass, F(1, 10))
        self.assertEqual(split.tail_inverse, F(6, 5))
        for cap in [4, 64, 256]:
            expected = F(1, 2) * min(1, F(256, cap**2)) + F(2, 5) * min(1, F(4096, cap**2))
            self.assertEqual(split.resolved_error(cap), expected)
        unresolved = law.split(F(1, 4), F(16), Precision())
        self.assertEqual(unresolved.unresolved_mass, F(1, 4))
        self.assertEqual(unresolved.tail_inverse, 0)
        self.assertEqual(unresolved.band_costs, split.band_costs)

    def test_exact_null_likelihood_is_a_probability_law(self):
        law = GapEnvelope([1, F(1, 2), F(1, 10)])
        for n in range(9):
            values = [law.null_prefix(h, n - h, F(1, 100)).upper for h in range(n + 1)]
            self.assertEqual(sum(comb(n, h) * p for h, p in enumerate(values)), 1)
            self.assertTrue(all(a >= b for a, b in zip(values, values[1:])))
            ratios = [F(3, 4)**h * F(1, 4)**(n-h) / values[h] for h in range(n + 1)]
            self.assertTrue(all(a <= b for a, b in zip(ratios, ratios[1:])))

    def test_zero_atom_fallback_does_not_divide_by_zero(self):
        for law in [GapEnvelope([1]), GapEnvelope([1, F(1, 4)])]:
            plan = plan_known_rare(law, rho=F(1, 4), budget=F(10**6))
            self.assertFalse(plan.levels)
            self.assertEqual(plan.mse_bound, F(1, 64))

    def test_invalid_bounds_plans_and_authorization(self):
        for bounds in [[], [F(1, 2)], [1, -1], [1, F(1, 2), F(3, 4)], [True]]:
            with self.assertRaises((ValueError, TypeError)):
                GapEnvelope(bounds)
        plan = plan_gap_envelope(3, rho="1/4", delta="1/20")
        forbidden = lambda _: self.fail("Unexpected acquisition")
        with self.assertRaises(ValueError):
            run_gap_envelope(plan, forbidden, budget=plan.flip_cap - 1)
        with self.assertRaises(ValueError):
            run_gap_envelope(replace(plan, coin_cap=1), forbidden, budget=plan.flip_cap)
        with self.assertRaises(ValueError):
            run_gap_envelope(replace(plan, probe_caps=(1,)), forbidden, budget=plan.flip_cap)
        with self.assertRaises(TypeError):
            run_gap_envelope(plan, forbidden, budget=plan.flip_cap, seed=True)

    def test_real_paid_learner_and_monotone_bounds(self):
        counts = [0, 0]

        def factory(rng):
            counts[0] += 1
            bit = rng.randrange(2)

            def flip():
                counts[1] += 1
                return bit

            return flip

        plan = plan_gap_envelope(6, rho="1/4", delta="1/20")
        result = run_gap_envelope(plan, factory, budget=plan.flip_cap, seed=3)
        self.assertEqual((result.items, result.flips), tuple(counts))
        self.assertLess(result.flips, plan.flip_cap)
        self.assertEqual(result.envelope.cdf, (F(1), F(1), F(1), F(1), F(8, 9), F(1, 2)))

    def test_work_is_not_assumed_monotone_but_correct_hitting_time_is(self):
        old = [0] * 16 + [1] * 48
        new = [0, 1] * 8 + [1] * 48
        self.assertTrue(all(a <= b for a, b in zip(old, new)))

        def ordinary(bits, ignore_wrong):
            heads = 0
            for n, bit in enumerate(bits, 1):
                heads += bit
                if n == 64:
                    return int(2 * heads > n), n
                if n & (n - 1) == 0 and _ordinary_stop(heads, n, 64):
                    if not ignore_wrong or 2 * heads > n:
                        return int(2 * heads > n), n

        self.assertEqual(ordinary(old, False), (0, 16))
        self.assertEqual(ordinary(new, False), (1, 32))
        self.assertEqual(ordinary(old, True), (1, 64))
        self.assertEqual(ordinary(new, True), (1, 32))

    def test_increasing_gaps_can_increase_entropy_across_a_band_boundary(self):
        # Split a point mass at 1/4: half stays, half moves just above the
        # boundary. This guards against claiming exact entropy monotonicity.
        original = cost_entropy([F(16)], Precision())
        increased = cost_entropy([F(8), F(1, 2) / F(2501, 10000)**2], Precision())
        self.assertGreater(increased.lower, original.upper)
        self.assertLessEqual(increased.upper, 3 * original.lower)


class ArbitraryLawControllerTests(unittest.TestCase):
    def test_no_pilot_before_its_full_reservation_fits(self):
        ladder = arbitrary_law_confidence(lambda _: self.fail("Unexpected acquisition"), rho="1/4", delta="1/20")
        out = ladder.advance_to(20)
        self.assertEqual(out.flips, 0)
        self.assertEqual(out.interval, ClosedInterval(0, F(1, 4)))
        self.assertEqual(ladder.advance_to(20), out)
        with self.assertRaises(ValueError):
            ladder.advance_to(19)

    def test_pilot_and_continuation_have_disjoint_coin_namespaces(self):
        seen = {}

        def pilot(plan):
            seen['plan'] = plan
            for query in [0, 0, 1]:
                yield query
            return GapEnvelope([1, F(1, 100)])

        def continuation(law, *, rho, cap, delta, rng):
            seen['law'], seen['cap'], seen['delta'] = law, cap, delta
            for query in [0, 1, 0]:
                yield query
            return ClosedInterval(F(1, 20), F(1, 5))

        counts = []

        def factory(rng):
            index = len(counts)
            counts.append(0)

            def flip():
                counts[index] += 1
                return 0

            return flip

        with patch('threshold_toolkit.arbitrary_law_confidence.gap_envelope_program', pilot), \
             patch('threshold_toolkit.arbitrary_law_confidence.known_law_interval', continuation):
            interval, used, made, timeout = _execute(
                arbitrary_law_interval(rho="1/4", cap=10000, delta="1/20", rng=Random(0)),
                factory, Random(0), 10000)
        self.assertFalse(timeout)
        self.assertEqual((used, made, counts), (6, 4, [2, 1, 2, 1]))
        self.assertEqual(interval, ClosedInterval(F(1, 20), F(1, 5)))
        self.assertEqual(seen['plan'].delta, F(1, 40))
        self.assertEqual(seen['delta'], F(1, 40))
        self.assertEqual(seen['cap'] + seen['plan'].flip_cap, 10000)

    def test_real_ladder_caps_and_callback_failures(self):
        counts = [0]

        def factory(rng):
            def flip():
                counts[0] += 1
                return 0
            return flip

        ladder = arbitrary_law_confidence(factory, rho="1/4", delta="1/20")
        for allowance in [0, 100, 1000, 10000]:
            state = ladder.advance_to(allowance)
            self.assertLessEqual(state.flips, state.reserved_budget)
            self.assertLessEqual(state.reserved_budget, allowance)
            self.assertEqual(state.flips, counts[0])
            self.assertTrue(state.interval.contains(0))
            self.assertEqual(ladder.advance_to(allowance), state)
        broken = arbitrary_law_confidence(lambda _: lambda: True, rho="1/4", delta="1/20")
        with self.assertRaises(ValueError):
            broken.advance_to(10000)
        with self.assertRaises(RuntimeError):
            broken.advance_to(10000)

    def test_known_law_radius_keeps_relative_precision_for_tiny_risk(self):
        plan = RarePlan(None, F(1, 4), F(1), (), (), F(1, 2**400))
        with patch('threshold_toolkit.known_law_confidence.plan_known_rare', return_value=plan):
            interval, used, made, timeout = _execute(
                known_law_interval(None, rho="1/4", cap=1000, delta="1/20", rng=Random(0)),
                lambda _: self.fail("Constant blocks need no coin"), Random(0), 1000)
        self.assertFalse(timeout)
        self.assertEqual((used, made), (0, 0))
        self.assertTrue(interval.contains(F(1, 8)))
        self.assertGreater(interval.width, 0)
        self.assertLess(interval.width, F(1, 2**190))
        self.assertGreaterEqual((interval.width / 2)**2, 8 * plan.mse_bound)


if __name__ == '__main__':
    unittest.main()
