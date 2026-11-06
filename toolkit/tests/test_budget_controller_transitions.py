"""Controller lifecycle and paid-observation regressions, not coverage proofs."""

from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction as F
from pathlib import Path
from random import Random
from threading import Event
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from threshold_toolkit.budget_ladders import RMSLadder, _execute
from threshold_toolkit.confidence_amplification import _run_block
from threshold_toolkit.confidence_ladders import ClosedInterval, ConfidenceLadder
from threshold_toolkit.finite_family_confidence import FiniteFamilyConfidenceLadder
from threshold_toolkit.law_identification import LawPilot, plan_law_pilot
from threshold_toolkit.rare_event_functional import FiniteGapLaw
from threshold_toolkit.tail_mass import TailMassProbe


LAWS = (FiniteGapLaw([("1/2", 1)]), FiniteGapLaw([("1/4", 1)]))
KINDS = ("rms", "confidence", "pilot", "tail", "family_pilot", "family_continuation")


def fixed_program(count, value):
    for _ in range(count):
        yield 0
    return value


def make_controller(kind, coins):
    if kind == "rms":
        return RMSLadder(lambda b, rng: fixed_program(4*b, F(1, 8)), coins)
    if kind == "confidence":
        return ConfidenceLadder(
            lambda cap, d, rng: fixed_program(cap, ClosedInterval(0, "1/4")),
            coins, delta="1/8")
    if kind == "pilot":
        return LawPilot(plan_law_pilot(LAWS, delta="1/8"), coins)
    if kind == "tail":
        return TailMassProbe(4, coins)
    candidates = LAWS if kind == "family_pilot" else LAWS[:1]
    return FiniteFamilyConfidenceLadder(candidates, coins, rho="1/4", delta="1/8")


class ControllerTransitionTests(unittest.TestCase):
    def setUp(self):
        # Exercise the family controller's continuation at small budgets without
        # requiring a statistically nonvacuous known-law estimator plan.
        def interval(law, *, rho, cap, delta, rng):
            return fixed_program(cap, ClosedInterval(0, rho))
        mocked = patch("threshold_toolkit.known_law_confidence.known_law_interval", interval)
        mocked.start()
        self.addCleanup(mocked.stop)

    def test_reentrant_source_callbacks_cannot_spend_or_authorize_more(self):
        for kind in KINDS:
            for location in ("factory", "flip"):
                with self.subTest(kind=kind, location=location):
                    entered, reads = [], []

                    def reenter():
                        if not entered:
                            entered.append(True)
                            for budget in (4, 12):
                                with self.assertRaisesRegex(RuntimeError, "already running"):
                                    controller.advance_to(budget)

                    def coins(rng):
                        if location == "factory":
                            reenter()
                        def flip():
                            reads.append(0)
                            if location == "flip":
                                reenter()
                            return 0
                        return flip

                    controller = make_controller(kind, coins)
                    state = controller.advance_to(4)
                    self.assertEqual((state.authorized_budget, state.flips, len(reads)), (4, 4, 4))
                    self.assertEqual(controller.advance_to(4), state)
                    self.assertEqual(controller.advance_to(12).flips, 12)
                    self.assertEqual(len(reads), 12)

    def test_reentrant_program_factory_body_and_finalizer_are_rejected(self):
        for kind in ("rms", "confidence"):
            for location in ("factory", "start", "send", "close"):
                with self.subTest(kind=kind, location=location):
                    entered = []

                    def reenter():
                        if not entered:
                            entered.append(True)
                            with self.assertRaisesRegex(RuntimeError, "already running"):
                                controller.advance_to(12)

                    def factory(*args):
                        if location == "factory":
                            reenter()
                        def program():
                            try:
                                if location == "start":
                                    reenter()
                                while True:
                                    yield 0
                                    if location == "send":
                                        reenter()
                            finally:
                                if location == "close":
                                    reenter()
                        return program()

                    coins = lambda rng: lambda: 0
                    controller = (RMSLadder(factory, coins) if kind == "rms" else
                                  ConfidenceLadder(factory, coins, delta="1/8"))
                    state = controller.advance_to(4)
                    self.assertEqual(entered, [True])
                    self.assertEqual((state.authorized_budget, state.flips), (4, 4))
                    self.assertTrue(state.runs[0].timed_out)

    def test_uncaught_reentry_invalidates_the_active_controller(self):
        for kind in KINDS:
            with self.subTest(kind=kind):
                calls = []
                def coins(rng):
                    calls.append(True)
                    if len(calls) == 1:
                        controller.advance_to(4)
                    return lambda: 0
                controller = make_controller(kind, coins)
                with self.assertRaisesRegex(RuntimeError, "already running"):
                    controller.advance_to(4)
                with self.assertRaisesRegex(RuntimeError, "invalidated"):
                    controller.advance_to(12)
                self.assertEqual(calls, [True])

    def test_overlapping_thread_call_is_rejected_without_mutating_active_run(self):
        for kind in KINDS:
            with self.subTest(kind=kind):
                waiting, release = Event(), Event()
                reads = []
                def coins(rng):
                    def flip():
                        reads.append(0)
                        if len(reads) == 1:
                            waiting.set()
                            if not release.wait(5):
                                raise RuntimeError("Test did not release the callback")
                        return 0
                    return flip
                controller = make_controller(kind, coins)
                with ThreadPoolExecutor(max_workers=1) as pool:
                    future = pool.submit(controller.advance_to, 4)
                    try:
                        self.assertTrue(waiting.wait(5))
                        with self.assertRaisesRegex(RuntimeError, "already running"):
                            controller.advance_to(12)
                    finally:
                        release.set()
                    state = future.result(timeout=5)
                self.assertEqual((state.authorized_budget, state.flips, len(reads)), (4, 4, 4))
                self.assertEqual(controller.advance_to(4), state)

    def test_callback_interrupts_invalidate_even_after_partial_consumption(self):
        for kind in KINDS:
            for error in (KeyboardInterrupt, SystemExit):
                for location in ("factory", "first_flip", "third_flip"):
                    with self.subTest(kind=kind, error=error, location=location):
                        reads, interrupted = [], []
                        def coins(rng):
                            if location == "factory" and not interrupted:
                                interrupted.append(True)
                                raise error("interrupted")
                            def flip():
                                reads.append(0)
                                if (location != "factory" and not interrupted
                                        and len(reads) == (1 if location == "first_flip" else 3)):
                                    interrupted.append(True)
                                    raise error("interrupted")
                                return 0
                            return flip
                        controller = make_controller(kind, coins)
                        with self.assertRaises(error):
                            controller.advance_to(4)
                        before = len(reads)
                        for budget in (4, 12):
                            with self.assertRaisesRegex(RuntimeError, "invalidated"):
                                controller.advance_to(budget)
                        self.assertEqual(len(reads), before)

    def test_invalid_budgets_are_recoverable_without_consuming_observations(self):
        for kind in KINDS:
            with self.subTest(kind=kind):
                reads = []
                def coins(rng):
                    def flip():
                        reads.append(0)
                        return 0
                    return flip
                controller = make_controller(kind, coins)
                state = controller.advance_to(4)
                for budget in (-1, True, 4.0, "12", 3, 1 << 4096):
                    with self.assertRaises(ValueError):
                        controller.advance_to(budget)
                    self.assertEqual(controller.advance_to(4), state)
                self.assertEqual(len(reads), 4)
                self.assertEqual(controller.advance_to(12).flips, 12)

    def test_confidence_exact_cap_and_timeout_spend_each_stage_once(self):
        closed, made = [], []
        def coins(rng):
            made.append(True)
            return lambda: 0
        def program(cap, delta, rng):
            try:
                for i in range(cap + (cap != 4)):
                    yield i
                return ClosedInterval("1/16", "3/16")
            finally:
                closed.append(cap)
        controller = ConfidenceLadder(program, coins, delta="1/8")
        first = controller.advance_to(4)
        final = controller.advance_to(12)
        self.assertEqual(final.interval, first.interval)
        self.assertEqual([r.timed_out for r in final.runs], [False, True])
        self.assertEqual((final.flips, final.reserved_budget, len(made)), (12, 12, 12))
        self.assertEqual(final.spent_failure_budget, F(1, 12))
        self.assertEqual(final.remaining_failure_budget, F(1, 24))
        self.assertEqual(controller.advance_to(12), final)
        self.assertEqual(closed, [4, 8])

    def test_cleanup_failure_invalidates_ladder_after_paid_work(self):
        for kind in ("rms", "confidence"):
            with self.subTest(kind=kind):
                closed = []
                def program(*args):
                    try:
                        while True:
                            yield 0
                    finally:
                        closed.append(True)
                        raise OSError("cleanup failed")
                coins = lambda rng: lambda: 0
                controller = (RMSLadder(program, coins) if kind == "rms" else
                              ConfidenceLadder(program, coins, delta="1/8"))
                with self.assertRaisesRegex(OSError, "cleanup failed"):
                    controller.advance_to(4)
                with self.assertRaisesRegex(RuntimeError, "invalidated"):
                    controller.advance_to(12)
                self.assertEqual(closed, [True])

    def test_terminal_pilot_and_probe_do_no_work_with_more_authorization(self):
        for kind in ("pilot", "singleton", "tail"):
            with self.subTest(kind=kind):
                reads = []
                def coins(rng):
                    def flip():
                        reads.append(0)
                        return 0
                    return flip
                if kind == "tail":
                    controller, cap = TailMassProbe(1, coins), 4
                else:
                    plan = plan_law_pilot(LAWS[:1] if kind == "singleton" else LAWS,
                                          delta="1/8")
                    controller, cap = LawPilot(plan, coins), plan.flip_cap
                first = controller.advance_to(cap)
                later = controller.advance_to(cap + 100)
                self.assertEqual((later.flips, len(reads)), (cap, cap))
                self.assertEqual(later.authorized_budget, cap + 100)
                if kind == "tail":
                    self.assertTrue(later.unresolved)
                    self.assertEqual(later.completed, first.completed)
                else:
                    self.assertIsNotNone(later.result)
                    self.assertEqual(later.result, first.result)


class ExecutorTransitionTests(unittest.TestCase):
    def test_both_executors_close_on_source_and_program_errors(self):
        for runner in ("ladder", "median"):
            for location in ("factory", "flip", "program", "invalid_bit", "invalid_query"):
                with self.subTest(runner=runner, location=location):
                    closed, reads = [], []
                    def program():
                        try:
                            yield 0
                            if location == "program":
                                raise OSError("program failed")
                            yield -1 if location == "invalid_query" else 0
                            return F(1, 8)
                        finally:
                            closed.append(True)
                    def coins(rng):
                        if location == "factory":
                            raise OSError("factory failed")
                        def flip():
                            reads.append(0)
                            if location == "flip":
                                raise OSError("flip failed")
                            return True if location == "invalid_bit" else 0
                        return flip
                    with self.assertRaises((OSError, ValueError)):
                        if runner == "ladder":
                            _execute(program(), coins, Random(0), 4)
                        else:
                            _run_block(program(), coins, Random(0), 4, F(1, 4))
                    self.assertEqual(closed, [True])
                    self.assertEqual(len(reads), 0 if location == "factory" else 1)


if __name__ == "__main__":
    unittest.main()
