"""Check the integer thresholds, observed interval endpoints and physical budget."""

from fractions import Fraction as F

from pathlib import Path
from random import Random
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from threshold_toolkit.confidence_ladders import ClosedInterval
from threshold_toolkit.unknown_law_confidence import (
    _hoeffding_count,
    _stage,
    unknown_law_confidence,
)


class UnknownLawConfidenceTests(unittest.TestCase):
    def test_threshold_is_least_sufficient_integer(self):
        for trials in [1, 2, 7, 64, 10**10]:
            for d in [F(1), F(1, 2), F(7, 15), F(1, 100), F(1, 2**150 + 1)]:
                h = _hoeffding_count(trials, d)
                self.assertGreaterEqual(d * 2 ** (2 * h * h // trials), 1)
                if h:
                    self.assertLess(d * 2 ** (2 * (h - 1) ** 2 // trials), 1)

    def test_positive_negative_and_threshold_ties(self):
        # 64 items of 64 flips. A count exactly at either threshold is unresolved.
        m = n = 64
        h = _hoeffding_count(m, F(1, n))
        heads = [m] * 16 + [0] * 32 + [m // 2 + h, m // 2 - h] * 8
        program = _stage(n * m + 1, F(1, 4), Random(0))
        item = next(program)
        for i, total in enumerate(heads):
            for k in range(m):
                self.assertEqual(item, i)
                if i == n - 1 and k == m - 1:
                    with self.assertRaises(StopIteration) as done:
                        program.send(int(k < total))
                else:
                    item = program.send(int(k < total))
        pad = F(_hoeffding_count(n, F(1, 12)) + 1, n)
        self.assertEqual(
            done.exception.value, ClosedInterval(F(1, 4) - pad, F(1, 2) + pad)
        )

    def test_unknown_law_ladder_on_observable_flips(self):
        seen = [0, 0]

        def factory(rng):
            seen[0] += 1

            def flip():
                seen[1] += 1
                return 0

            return flip

        ladder = unknown_law_confidence(factory, delta="1/4", seed=81)
        initial = ladder.advance_to(3)
        self.assertEqual(initial.interval, ClosedInterval(0, 1))
        partial = ladder.advance_to(8187)
        last = ladder.advance_to(8188)
        self.assertLessEqual(last.interval.upper, partial.interval.upper)
        self.assertTrue(last.interval.contains(0))
        self.assertLess(last.interval.width, F(1, 2))
        self.assertEqual(last.flips, seen[1])
        self.assertLessEqual(last.flips, 8188)
        self.assertEqual(sum(run.created_coins for run in last.runs), seen[0])
        self.assertFalse(any(run.timed_out for run in last.runs))
        self.assertEqual(ladder.advance_to(8188), last)
