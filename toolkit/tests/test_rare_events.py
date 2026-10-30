"""Analytic and numerical regression tests for the finite-law rate calculator."""

import dataclasses
import math
import subprocess
import sys
import unittest
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from threshold_toolkit import FiniteGapLaw, RareEventProfile
from threshold_toolkit.rare_events import QUANTILE_SELECTION_FACTOR


class FiniteLawTests(unittest.TestCase):
    def test_normalizes_sorts_merges_and_drops_zero_weights(self):
        law = FiniteGapLaw([0.25, 0.125, 0.25, 0.4], [2, 1, 1, 0])
        self.assertEqual(law.gaps, (0.125, 0.25))
        self.assertEqual(law.weights, (0.25, 0.75))
        self.assertEqual(FiniteGapLaw([0.25, 0.125, 0.25]).weights, (1 / 3, 2 / 3))
        self.assertEqual(FiniteGapLaw([0.125, 0.25], [1e308, 1e308]).weights, (0.5, 0.5))
        with self.assertRaises(dataclasses.FrozenInstanceError):
            law.weights = (1.0,)

    def test_invalid_laws_are_rejected(self):
        cases = [([], None), ([0], None), ([-0.1], None), ([0.50001], None),
                 ([math.inf], None), ([math.nan], None), ([0.25], []),
                 ([0.25], [0]), ([0.25], [-1]), ([0.25], [math.inf]),
                 ([0.25], [math.nan]), ([0.25, 0.125], [1e308, 5e-324])]
        for gaps, weights in cases:
            with self.subTest(gaps=gaps, weights=weights), self.assertRaises(ValueError):
                FiniteGapLaw(gaps, weights)

    def test_fractional_quantile_atom_is_split(self):
        profile = FiniteGapLaw([0.125, 0.25, 0.5], [1, 3, 12]).profile(0.125)
        self.assertEqual(profile.quantile_gap, 0.25)
        self.assertEqual(profile.tail_weights, (0.0625, 0.0625, 0.0))
        self.assertEqual(profile.core_weights, (0.0, 0.125, 0.75))
        self.assertEqual(math.fsum(profile.tail_weights), profile.rho)
        for tail, core, weight in zip(profile.tail_weights, profile.core_weights, profile.law.weights):
            self.assertEqual(tail + core, weight)

    def test_exact_quantile_boundary_and_tiny_earlier_atom(self):
        profile = FiniteGapLaw([0.125, 0.25, 0.5], [0.125, 0.125, 0.75]).profile(0.25)
        self.assertEqual(profile.quantile_gap, 0.25)
        self.assertEqual(profile.tail_weights, (0.125, 0.125, 0.0))
        # A tiny first atom is not lost by subtracting it from a large remainder.
        profile = FiniteGapLaw([1e-200, 0.25], [1e-100, 1]).profile(0.125)
        self.assertEqual(profile.tail_weights[0], 1e-100)
        self.assertEqual(profile.core_weights[0], 0)
        self.assertEqual(profile.quantile_gap, 0.25)

    def test_package_execution_and_rate_api_need_only_standard_library(self):
        toolkit = str(Path(__file__).resolve().parents[1])
        code = ("import sys; sys.path.insert(0, sys.argv[1]); "
                "from threshold_toolkit import FiniteGapLaw, RareEventProfile, estimate_fraction; "
                "assert RareEventProfile(FiniteGapLaw([.25]),.1).rate(100)>0; "
                "assert 'numpy' not in sys.modules and 'scipy' not in sys.modules")
        completed = subprocess.run([sys.executable, "-S", "-c", code, toolkit],
                                   capture_output=True, text=True)
        self.assertEqual(completed.returncode, 0, completed.stderr)


class QuantileFormulaTests(unittest.TestCase):
    def test_single_atom_matches_closed_form_at_all_budget_scales(self):
        for gap in (0.5, 0.25, 0.01, 1e-100):
            for rho in (0.25, 0.1, 1e-20):
                profile = FiniteGapLaw([gap]).profile(rho)
                self.assertEqual(profile.scale_entropy, 0)
                for budget in (1e-10, 1, 1e3, 1e10, 1e100, 1e300):
                    expected = min(rho, (rho + math.sqrt(rho * (1 - rho))) / gap / math.sqrt(budget))
                    observed = profile.rate(budget)
                    with self.subTest(gap=gap, rho=rho, budget=budget):
                        self.assertAlmostEqual(observed / expected, 1, delta=2e-13)

    def test_entropy_uses_bands_not_atoms(self):
        profile = FiniteGapLaw([0.3, 0.4, 0.5], [1, 2, 3]).profile(0.1)
        self.assertEqual(len(profile.bands), 1)
        self.assertEqual(profile.bands[0].index, 0)
        self.assertEqual(profile.scale_entropy, 0)
        expected = math.fsum(weight / gap ** 2
                             for gap, weight in zip(profile.law.gaps, profile.core_weights))
        self.assertAlmostEqual(profile.core_entropy, expected)

    def test_dyadic_endpoints_and_neighbors_have_the_right_band(self):
        for power in (1, 2, 20, 500, 1074):
            gap = math.ldexp(1, -power)
            self.assertEqual(FiniteGapLaw([gap]).profile(0.1).bands[0].index, power - 1)
            above = math.nextafter(gap, math.inf)
            if above <= 0.5:
                self.assertEqual(FiniteGapLaw([above]).profile(0.1).bands[0].index, power - 2)
            below = math.nextafter(gap, 0)
            if below > 0:
                # Adjacent subnormal floats can cross more than one dyadic
                # boundary; use the direct power only above the smallest bin.
                expected = power - 1 if power < 1074 else power
                self.assertEqual(FiniteGapLaw([below]).profile(0.1).bands[0].index, expected)

    def test_tail_and_entropy_components_match_direct_formula(self):
        profile = FiniteGapLaw([0.001, 0.02, 0.05, 0.3], [0.05, 0.1, 0.2, 0.65]).profile(0.25)
        costs = [weight / gap ** 2 for weight, gap in zip(profile.core_weights, profile.law.gaps) if weight]
        total = math.fsum(costs)
        gamma = total + math.fsum(cost * math.log(total / cost) for cost in costs)
        self.assertAlmostEqual(profile.core_entropy / gamma, 1, places=13)
        previous = math.inf
        for budget in (0.1, 10, 1e3, 1e5, 1e7, 1e12):
            h = 1 / math.sqrt(budget)
            tail = math.fsum(weight * min(1, h / gap)
                            for weight, gap in zip(profile.tail_weights, profile.law.gaps))
            component = h * math.sqrt(profile.rho * gamma)
            result = profile.evaluate(budget)
            self.assertAlmostEqual(result.tail / tail, 1, places=13)
            self.assertAlmostEqual(result.entropy_term / component, 1, places=13)
            self.assertAlmostEqual(result.value, min(profile.rho, tail + component), places=13)
            self.assertLessEqual(result.value, previous)
            self.assertEqual(result.selection_upper, result.value)
            self.assertEqual(result.selection_lower,
                             max(result.tail, result.value / QUANTILE_SELECTION_FACTOR))
            previous = result.value

    def test_h_at_quantile_boundary_saturates(self):
        profile = FiniteGapLaw([0.125, 0.25, 0.5], [0.05, 0.2, 0.75]).profile(0.1)
        for budget in (0.1, 1, 1 / profile.quantile_gap ** 2):
            result = profile.evaluate(budget)
            self.assertEqual(result.value, profile.rho)
            self.assertEqual((result.selection_lower, result.selection_upper),
                             (profile.rho, profile.rho))

    def test_tiny_gaps_keep_finite_capped_rate_and_log_diagnostics(self):
        profile = FiniteGapLaw([5e-324]).profile(0.125)
        self.assertTrue(math.isinf(profile.core_cost))
        self.assertTrue(math.isinf(profile.core_entropy))
        self.assertTrue(math.isfinite(profile.log_core_entropy))
        self.assertEqual(profile.rate(1e308), 0.125)
        self.assertTrue(math.isfinite(profile.evaluate(1).value))


class RateInversionTests(unittest.TestCase):
    def test_one_atom_budget_has_closed_form(self):
        profile = FiniteGapLaw([0.125]).profile(0.1)
        for target in (0.09, 0.01, 1e-100):
            expected = ((0.1 + math.sqrt(0.09)) / (0.125 * target)) ** 2
            result = profile.budget_for_rate(target)
            self.assertEqual(result.status, "finite")
            self.assertAlmostEqual(result.budget / expected, 1, delta=2e-13)

    def test_roundtrip_across_piecewise_segments(self):
        profile = FiniteGapLaw([0.00001, 0.001, 0.25], [0.02, 0.05, 0.93]).profile(0.25)
        for target in (0.249, 0.2, 0.08, 0.07, 0.06, 0.03, 0.02, 0.01, 1e-100):
            result = profile.budget_for_rate(target)
            self.assertEqual(result.status, "finite")
            with self.subTest(target=target):
                self.assertAlmostEqual(profile.rate(result.budget) / target, 1, delta=2e-13)
                self.assertGreater(profile.rate(result.budget * 0.99), target)
                self.assertLess(profile.rate(result.budget * 1.01), target)

    def test_saturation_and_overflow_are_explicit(self):
        profile = FiniteGapLaw([0.25]).profile(0.1)
        for target in (0.1, 0.25, 10):
            result = profile.budget_for_rate(target)
            self.assertEqual((result.status, result.budget, result.log_budget),
                             ("saturated", 0, -math.inf))
        for profile, target in ((profile, 1e-200), (FiniteGapLaw([5e-324]).profile(0.1), 0.01)):
            result = profile.budget_for_rate(target)
            self.assertEqual(result.status, "overflow")
            self.assertEqual(result.budget, math.inf)
            self.assertTrue(math.isfinite(result.log_budget))

    def test_tiny_atoms_do_not_turn_inverse_remainder_into_zero(self):
        profile = FiniteGapLaw([1e-300, 1e-100, 1e-50, 0.25],
                               [0.01, 1e-20, 1e-20, 0.99]).profile(0.1)
        # Several rounded prefix masses equal the target.  They exceed it
        # in exact arithmetic, so the solution is in the first segment.
        result = profile.budget_for_rate(0.01)
        self.assertEqual(result.status, "overflow")
        self.assertAlmostEqual(result.log_budget, -2 * math.log(1e-300), places=10)
        below = profile.budget_for_rate(math.nextafter(0.01, 0))
        self.assertEqual(below.status, "overflow")
        above = math.nextafter(0.01, math.inf)
        result = profile.budget_for_rate(above)
        self.assertEqual(result.status, "finite")
        # Immediately above the plateau, losing the tiny atoms from the
        # target-prefix subtraction would move this budget by about 2%.
        remainder = float(Fraction(above) - sum(map(Fraction, profile.tail_weights[:3])))
        slope = math.sqrt(profile.rho * profile.core_entropy) + profile.tail_weights[3] / 0.25
        self.assertAlmostEqual(result.budget / (slope / remainder) ** 2, 1, delta=2e-13)

    def test_invalid_rarity_budget_and_target(self):
        law = FiniteGapLaw([0.25])
        for rho in (0, -1, 0.250001, math.nan, math.inf):
            with self.subTest(rho=rho), self.assertRaises(ValueError):
                law.profile(rho)
        profile = law.profile(0.1)
        for bad in (0, -1, math.nan, math.inf, "invalid"):
            with self.subTest(budget=bad), self.assertRaises(ValueError):
                profile.evaluate(bad)
            with self.subTest(target=bad), self.assertRaises(ValueError):
                profile.budget_for_rate(bad)


if __name__ == "__main__":
    unittest.main()
