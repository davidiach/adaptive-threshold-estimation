"""Regression tests for the known-law integrals used by the rare-event construction."""

from fractions import Fraction as F
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from threshold_toolkit.known_law_oracle import FiniteGapOracle
from threshold_toolkit.rare_event_functional import (
    FiniteGapLaw,
    Interval,
    Precision,
    band_index,
)


class FiniteGapOracleTests(unittest.TestCase):
    def test_fractional_quantile_and_work_boundary(self):
        law = FiniteGapLaw([("1/16", "1/8"), ("1/4", "1/2"), ("1/2", "3/8")])
        design = FiniteGapOracle(law).split(F(1, 4), F(16), Precision())
        self.assertEqual(design.unresolved_mass, F(1, 8))
        self.assertEqual(design.tail_inverse, F(1, 2))
        self.assertEqual(
            design.band_costs, {band_index(F(1, 4)): F(6), band_index(F(1, 2)): F(3, 2)}
        )
        self.assertEqual(design.resolved_error(4), F(7, 8))
        self.assertEqual(design.resolved_error(64), F(1, 32) + F(3, 2048))
        self.assertEqual(design.tail_work(4), F(1, 2))

    def test_null_likelihood_uses_all_mass_even_at_maximal_gap(self):
        oracle = FiniteGapOracle(FiniteGapLaw([("1/4", "1/2"), ("1/2", "1/2")]))
        for heads, tails, expected in [
            (0, 0, F(1)),
            (1, 0, F(1, 8)),
            (0, 1, F(7, 8)),
            (1, 1, F(3, 32)),
        ]:
            self.assertEqual(
                oracle.null_prefix(heads, tails, F(1, 100)),
                Interval(expected, expected),
            )
