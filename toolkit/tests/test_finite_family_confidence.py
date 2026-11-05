"""Execution and accounting regressions, not a statistical coverage proof."""

from fractions import Fraction as F
from pathlib import Path
from random import Random
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from threshold_toolkit.budget_ladders import _execute
from threshold_toolkit.confidence_ladders import ClosedInterval
from threshold_toolkit.finite_family_confidence import FiniteFamilyConfidenceLadder
from threshold_toolkit.known_law_confidence import (
    _capped_block, known_law_interval, known_law_ladder,
)
from threshold_toolkit.known_law_oracle import FiniteGapOracle
from threshold_toolkit.known_rare_estimator import Level, RarePlan
from threshold_toolkit.law_identification import LawPilot, plan_law_pilot, run_law_pilot
from threshold_toolkit.rare_event_functional import FiniteGapLaw


LAWS = (FiniteGapLaw([("1/2", 1)]), FiniteGapLaw([("1/4", 1)]))


class Source:
    def __init__(self):
        self.reads = []
        self.tape = []

    def __call__(self, rng):
        label = len(self.reads)
        self.reads.append(0)
        # Independent deterministic-gap coins with random signs.
        bit = rng.randrange(2)

        def flip():
            self.reads[label] += 1
            self.tape.append((label, bit))
            return bit

        return flip


class PilotContinuationTests(unittest.TestCase):
    def test_every_pilot_pause_matches_one_shot_and_preserves_coins(self):
        plan = plan_law_pilot(LAWS, delta="1/8")
        one, paused = Source(), Source()
        expected = run_law_pilot(plan, one, budget=plan.flip_cap, seed=12)
        pilot = LawPilot(plan, paused, seed=12)
        for budget in range(plan.flip_cap + 1):
            state = pilot.advance_to(budget)
            self.assertEqual(state.flips, budget)
            self.assertEqual(len(paused.tape), budget)
            self.assertEqual(pilot.advance_to(budget), state)
            self.assertEqual(state.result is None, budget < plan.flip_cap)
        self.assertEqual(state.result, expected)
        self.assertEqual(one.tape, paused.tape)
        self.assertEqual(paused.reads, [2] * plan.samples_per_moment)

    def test_four_flip_prefix_survives_odd_pause(self):
        candidates = (FiniteGapLaw([("1/4", 1)]),
                      FiniteGapLaw([("1/8", "4/5"), ("1/2", "1/5")]))
        plan = plan_law_pilot(candidates, delta="1/4")
        source = Source()
        pilot = LawPilot(plan, source)
        for b in (1, 3, 4, 5, 8):
            self.assertEqual(pilot.advance_to(b).flips, b)
        self.assertEqual(source.reads, [4, 4])
        self.assertIsNone(pilot.advance_to(8).result)

    def test_pilot_rejects_decreasing_budget_and_invalidates_on_failure(self):
        plan = plan_law_pilot(LAWS, delta="1/8")
        pilot = LawPilot(plan, Source())
        pilot.advance_to(3)
        with self.assertRaises(ValueError):
            pilot.advance_to(2)
        self.assertEqual(pilot.advance_to(4).flips, 4)
        for factory in (lambda _: None, lambda _: lambda: True):
            failed = LawPilot(plan, factory)
            with self.assertRaises((TypeError, ValueError)):
                failed.advance_to(1)
            with self.assertRaises(RuntimeError):
                failed.advance_to(2)

    def test_combined_budget_and_selection_pass_to_continuation(self):
        calls = []

        def stage(law, *, rho, cap, delta, rng):
            calls.append((law.law, rho, cap, delta))
            for _ in range(cap):
                yield 0
            return ClosedInterval("1/16", "3/16")

        source = Source()
        ladder = FiniteFamilyConfidenceLadder(LAWS, source, rho="1/4", delta="1/8")
        h = ladder.plan.flip_cap
        with patch("threshold_toolkit.known_law_confidence.known_law_interval", stage):
            for budget in (0, 1, h - 1, h, h + 3, h + 4, h + 12):
                state = ladder.advance_to(budget)
                self.assertEqual(state.flips, len(source.tape))
                self.assertLessEqual(state.flips, state.reserved_budget)
                self.assertLessEqual(state.reserved_budget, budget)
                if budget < h:
                    self.assertIsNone(state.selected)
                    self.assertIsNone(state.continuation)
                    self.assertEqual(state.interval, ClosedInterval(0, "1/4"))
                else:
                    self.assertEqual(state.selected, 0)
                    self.assertEqual(state.continuation.authorized_budget, budget - h)
            self.assertEqual(ladder.advance_to(h + 12), state)
        self.assertEqual(calls, [(LAWS[0], F(1, 4), 4, F(1, 32)),
                                (LAWS[0], F(1, 4), 8, F(1, 96))])
        self.assertEqual(source.reads, [2] * ladder.plan.samples_per_moment + [4, 8])
        self.assertEqual(state.interval, ClosedInterval("1/16", "3/16"))

    def test_combined_jump_and_incremental_runs_are_identical(self):
        def stage(law, *, rho, cap, delta, rng):
            for i in range(cap):
                yield rng.randrange(i + 1)
            return ClosedInterval(0, rho)

        a, b = Source(), Source()
        left = FiniteFamilyConfidenceLadder(LAWS, a, rho="1/4", delta="1/8", seed=92)
        right = FiniteFamilyConfidenceLadder(LAWS, b, rho="1/4", delta="1/8", seed=92)
        end = left.plan.flip_cap + 60
        with patch("threshold_toolkit.known_law_confidence.known_law_interval", stage):
            expected = left.advance_to(end)
            for n in range(end + 1):
                actual = right.advance_to(n)
        self.assertEqual(actual, expected)
        self.assertEqual(a.tape, b.tape)

    def test_nonfirst_candidate_is_used_by_the_continuation(self):
        made = 0
        seen = []

        def factory(rng):
            nonlocal made
            bits = iter((0, 0 if made % 8 < 5 else 1))
            made += 1
            return bits.__next__

        def stage(law, *, rho, cap, delta, rng):
            seen.append(law.law)
            if False:
                yield 0
            return ClosedInterval(0, rho)

        ladder = FiniteFamilyConfidenceLadder(LAWS, factory, rho="1/4", delta="1/8")
        with patch("threshold_toolkit.known_law_confidence.known_law_interval", stage):
            state = ladder.advance_to(ladder.plan.flip_cap + 4)
        self.assertEqual(state.selected, 1)
        self.assertEqual(seen, [LAWS[1]])

    def test_fallback_and_empty_intersections_remain_capped_and_nested(self):
        def stage(law, *, rho, cap, delta, rng):
            yield 0
            return ClosedInterval(0, "1/16") if cap == 4 else ClosedInterval("3/16", rho)

        # Alternating flips produce parity -1, outside every candidate signature.
        def factory(rng):
            tape = iter((0, 1))
            return tape.__next__

        ladder = FiniteFamilyConfidenceLadder(LAWS, factory, rho="1/4", delta="1/8")
        h = ladder.plan.flip_cap
        with patch("threshold_toolkit.known_law_confidence.known_law_interval", stage):
            first = ladder.advance_to(h + 4)
            empty = ladder.advance_to(h + 12)
            last = ladder.advance_to(h + 28)
        self.assertEqual(first.selected, 0)
        self.assertTrue(empty.interval.empty)
        self.assertTrue(last.interval.empty)
        self.assertLessEqual(last.flips, h + 28)

    def test_singleton_zero_cost_and_error_invalidation(self):
        ladder = FiniteFamilyConfidenceLadder(LAWS[:1], Source(), rho="1/4", delta="1/8")
        zero = ladder.advance_to(0)
        self.assertEqual((zero.selected, zero.flips, ladder.plan.flip_cap), (0, 0, 0))
        self.assertEqual(ladder.advance_to(4).flips, 0)  # Vacuous known-law stage.
        with self.assertRaises(ValueError):
            ladder.advance_to(3)

        def broken(law, *, rho, cap, delta, rng):
            yield 0
            raise ValueError("callback failure")

        with patch("threshold_toolkit.known_law_confidence.known_law_interval", broken):
            with self.assertRaisesRegex(ValueError, "callback failure"):
                ladder.advance_to(12)
            with self.assertRaises(RuntimeError):
                ladder.advance_to(28)


class KnownLawStageTests(unittest.TestCase):
    def test_median_blocks_have_disjoint_coins_and_outward_radius(self):
        law = FiniteGapOracle(LAWS[0])
        p = RarePlan(law, F(1, 4), F(2), ((0, F(1)),),
                     (Level(1, F(1, 64), F(2), F(1)),), F(1, 10000))
        reads = []

        def factory(rng):
            i = len(reads)
            reads.append(0)

            def flip():
                reads[i] += 1
                return 0

            return flip

        with patch("threshold_toolkit.known_law_confidence.plan_known_rare", return_value=p):
            program = known_law_interval(law, rho="1/4", cap=99,
                                         delta="1/4", rng=Random(41))
            interval, used, made, timeout = _execute(program, factory, Random(42), 99)
        self.assertEqual((used, made, timeout), (22, 11, False))
        self.assertEqual(reads, [2] * 11)
        self.assertEqual(interval.lower, 0)
        self.assertGreaterEqual(interval.upper**2, 8 * p.mse_bound)
        self.assertLess(interval.upper, F(3, 100))

    def test_real_estimator_stage_is_nonvacuous_and_physically_accounted(self):
        reads = []

        def factory(rng):
            i = len(reads)
            reads.append(0)

            def flip():
                reads[i] += 1
                return 0

            return flip

        law = FiniteGapOracle(LAWS[0])
        program = known_law_interval(law, rho="1/4", cap=2**24,
                                     delta="1/4", rng=Random(41))
        interval, used, made, timeout = _execute(program, factory, Random(42), 2**24)
        self.assertFalse(timeout)
        self.assertEqual((used, made), (sum(reads), len(reads)))
        self.assertGreater(used, 0)
        self.assertLessEqual(used, 2**24)
        self.assertTrue(interval.contains(0))
        self.assertLess(interval.width, F(1, 4))

    def test_block_cap_between_classifier_pair_and_exact_completion(self):
        law = FiniteGapOracle(LAWS[0])
        p = RarePlan(law, F(1, 4), F(2), ((0, F(1)),),
                     (Level(1, F(1, 64), F(2), F(1)),), F(1))
        for cap, expected in [(1, F(1, 8)), (2, F(1, 4))]:
            program = _capped_block(p, Random(0), cap, offset=7)
            queries = []
            try:
                query = next(program)
                while True:
                    queries.append(query)
                    query = program.send(1)
            except StopIteration as done:
                self.assertEqual(done.value, (expected, 1))
            self.assertEqual(queries, [7] * cap)

    def test_invalid_inputs_do_not_sample(self):
        def forbidden(rng):
            self.fail("No sampling is authorized")

        for value in (0, "1/2", True, 0.1):
            with self.assertRaises((TypeError, ValueError)):
                FiniteFamilyConfidenceLadder(LAWS, forbidden, rho=value, delta="1/8")
            with self.assertRaises((TypeError, ValueError)):
                FiniteFamilyConfidenceLadder(LAWS, forbidden, rho="1/4", delta=value)
        with self.assertRaises(TypeError):
            known_law_ladder(object(), forbidden, rho="1/4", delta="1/8")
        with self.assertRaises(TypeError):
            FiniteFamilyConfidenceLadder(LAWS, forbidden, rho="1/4", delta="1/8", seed=True)


if __name__ == "__main__":
    unittest.main()
