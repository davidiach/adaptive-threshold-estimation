"""Independent rational/Decimal oracles for the finite-law rate calculator.

The production implementation groups logarithmic costs and uses prefix/suffix
queries.  These tests instead integrate rational atom masses directly and
evaluate logarithms at 90 decimal digits.  Exhaustive subset minimization is
only a small-instance check of the deterministic comparison, not a statistical
minimax proof or a replacement for the argument in the accompanying note.
"""

from decimal import Decimal, localcontext
from fractions import Fraction
import math
from pathlib import Path
import random
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from threshold_toolkit.rare_events import FiniteGapLaw, RareEventProfile


def decimal(value):
    """Convert a rational exactly before the active Decimal context rounds it."""
    value = Fraction(value)
    return Decimal(value.numerator) / Decimal(value.denominator)


def normalized_atoms(gaps, weights):
    total = sum(map(Fraction, weights))
    grouped = {}
    for gap, weight in zip(gaps, weights):
        gap, weight = Fraction(gap), Fraction(weight) / total
        if weight:
            grouped[gap] = grouped.get(gap, Fraction(0)) + weight
    return tuple(sorted(grouped.items()))


def band(gap):
    # Intentionally use exact endpoint comparisons, independently of frexp.
    index, upper = 0, Fraction(1, 2)
    while gap <= upper / 2:
        upper /= 2
        index += 1
    return index


def gamma(atoms):
    costs = {}
    for gap, weight in atoms:
        if weight:
            index = band(gap)
            costs[index] = costs.get(index, Fraction(0)) + weight / gap ** 2
    if not costs:
        return Decimal(0)
    total = sum(costs.values())
    return decimal(total) + sum((decimal(cost) * decimal(total / cost).ln()
                                 for cost in costs.values()), Decimal(0))


def split(atoms, rho):
    remaining, tail, core = Fraction(rho), [], []
    for gap, weight in atoms:
        taken = min(weight, remaining)
        tail.append((gap, taken))
        core.append((gap, weight - taken))
        remaining -= taken
    if remaining:
        raise ValueError("insufficient mass")
    return tuple(tail), tuple(core)


def tail_cost(atoms, h):
    return sum((decimal(weight) * min(Decimal(1), h / decimal(gap))
                for gap, weight in atoms), Decimal(0))


def quantile_value(atoms, rho, budget):
    tail, core = split(atoms, rho)
    h = Decimal(1) / decimal(budget).sqrt()
    ordinary = tail_cost(tail, h)
    entropy = h * (decimal(rho) * gamma(core)).sqrt()
    return min(decimal(rho), ordinary + entropy), ordinary, entropy


def hard_selection(atoms, rho, budget):
    """Enumerate every vertex of the finite submeasure box."""
    h = Decimal(1) / decimal(budget).sqrt()
    best = decimal(rho)
    for mask in range(1 << len(atoms)):
        kept = [atom for i, atom in enumerate(atoms) if mask & (1 << i)]
        rejected = [atom for i, atom in enumerate(atoms) if not mask & (1 << i)]
        value = h * (decimal(rho) * gamma(kept)).sqrt() + tail_cost(rejected, h)
        best = min(best, value)
    return best


class RareEventOracleTests(unittest.TestCase):
    def assert_decimal_close(self, actual, expected, relative=3e-13):
        self.assertTrue(math.isfinite(actual), (actual, expected))
        if expected == 0:
            self.assertEqual(actual, 0)
        else:
            difference = abs(Decimal.from_float(actual) / expected - 1)
            self.assertLessEqual(difference, Decimal(str(relative)), (actual, expected))

    def test_quantile_components_against_direct_high_precision_integration(self):
        cases = (
            # Several atoms share a band; entropy belongs to bands, not atoms.
            ([0.5, 0.375, 0.25, 0.1875, 0.125], [2, 1, 3, 1, 1], 0.25),
            # The rho boundary splits an atom, rather than rounding whole atoms.
            ([0.5, 0.25, 0.03125], [5, 2, 1], 0.1875),
            # Published noninterval-selection example; no threshold search can
            # substitute for the hard-selection oracle in the next test.
            ([0.5, 0.25, 0.125], [1023, 2, 1023], 0.25),
        )
        with localcontext() as context:
            context.prec = 90
            for gaps, weights, rho in cases:
                atoms = normalized_atoms(gaps, weights)
                profile = RareEventProfile(FiniteGapLaw(gaps, weights), rho)
                tail, core = split(atoms, rho)
                expected_bands = {band(gap) for gap, weight in core if weight}
                self.assertEqual({item.index for item in profile.bands}, expected_bands)
                self.assert_decimal_close(profile.core_entropy, gamma(core))
                for budget in (1, 16, 256, 4096, 2 ** 24):
                    expected, ordinary, entropy = quantile_value(atoms, rho, budget)
                    actual = profile.evaluate(budget)
                    with self.subTest(gaps=gaps, rho=rho, budget=budget):
                        self.assert_decimal_close(actual.tail, ordinary)
                        self.assert_decimal_close(actual.entropy_term, entropy)
                        self.assert_decimal_close(actual.value, expected)

    def test_selection_bracket_against_every_hard_assignment(self):
        rng = random.Random(27301)
        pool = [0.5, 0.375, 0.25, 0.1875, 0.125, 0.09375, 0.0625, 0.03125]
        cases = [([0.5, 0.25, 0.125], [1023, 2, 1023], 0.25)]
        for index in range(12):
            gaps = rng.sample(pool, 3 + index % 4)
            weights = [rng.randrange(1, 17) for _ in gaps]
            cases.append((gaps, weights, (0.25, 0.125, 0.0625)[index % 3]))
        with localcontext() as context:
            context.prec = 90
            for gaps, weights, rho in cases:
                atoms = normalized_atoms(gaps, weights)
                profile = RareEventProfile(FiniteGapLaw(gaps, weights), rho)
                for budget in (1, 64, 1024, 65536):
                    exact = hard_selection(atoms, rho, budget)
                    result = profile.evaluate(budget)
                    tolerance = exact * Decimal('4e-13')
                    with self.subTest(gaps=gaps, rho=rho, budget=budget):
                        self.assertLessEqual(Decimal.from_float(result.selection_lower), exact + tolerance)
                        self.assertGreaterEqual(Decimal.from_float(result.selection_upper), exact - tolerance)

    def test_dyadic_endpoints_and_adjacent_floats(self):
        with localcontext() as context:
            context.prec = 90
            for exponent in (1, 2, 7, 100, 500, 1022, 1073, 1074):
                endpoint = math.ldexp(1.0, -exponent)
                neighbors = {endpoint, math.nextafter(endpoint, 0.0),
                             math.nextafter(endpoint, math.inf)}
                for gap in sorted(gap for gap in neighbors if 0 < gap <= 0.5):
                    profile = RareEventProfile(FiniteGapLaw([gap]), 0.25)
                    expected_index = band(Fraction(gap))
                    expected_log = decimal(Fraction(3, 4) / Fraction(gap) ** 2).ln()
                    with self.subTest(exponent=exponent, gap=gap):
                        self.assertEqual(len(profile.bands), 1)
                        self.assertEqual(profile.bands[0].index, expected_index)
                        self.assertAlmostEqual(profile.log_core_entropy, float(expected_log), delta=8e-13)

    def test_duplicate_permutation_and_weight_scale_invariance(self):
        reference = RareEventProfile(FiniteGapLaw([0.03125, 0.125, 0.5], [1, 3, 4]), 0.25)
        variants = (
            ([0.5, 0.125, 0.03125], [4, 3, 1]),
            ([0.125, 0.5, 0.03125, 0.125, 0.5], [1, 1, 1, 2, 3]),
            ([0.03125, 0.125, 0.5], [1e300, 3e300, 4e300]),
            ([0.03125, 0.125, 0.5, 0.25], [1, 3, 4, 0]),
        )
        for gaps, weights in variants:
            profile = RareEventProfile(FiniteGapLaw(gaps, weights), 0.25)
            self.assertEqual(profile.law.gaps, reference.law.gaps)
            self.assertEqual(profile.quantile_gap, reference.quantile_gap)
            for budget in (1, 128, 8192, 2 ** 32):
                self.assertAlmostEqual(profile.rate(budget) / reference.rate(budget), 1, delta=3e-14)

    def test_extreme_weight_gap_products_remain_representable(self):
        gap, weight = math.ldexp(1.0, -500), math.ldexp(1.0, -1000)
        rho = math.ldexp(1.0, -1002)
        profile = RareEventProfile(FiniteGapLaw([gap, 0.5], [weight, 1]), rho)
        with localcontext() as context:
            context.prec = 90
            atoms = normalized_atoms([gap, 0.5], [weight, 1])
            expected, ordinary, entropy = quantile_value(atoms, rho, 1e308)
            actual = profile.evaluate(1e308)
            self.assertGreater(actual.value, 0)
            self.assertLess(actual.value, rho)
            self.assert_decimal_close(actual.tail, ordinary, relative=2e-12)
            self.assert_decimal_close(actual.entropy_term, entropy, relative=2e-12)
            self.assert_decimal_close(actual.value, expected, relative=2e-12)

    def test_overflow_is_a_representation_limit_with_correct_logarithm(self):
        gap = math.nextafter(0.0, 1.0)
        profile = RareEventProfile(FiniteGapLaw([gap]), 0.25)
        self.assertTrue(math.isinf(profile.core_entropy))
        result = profile.budget_for_rate(0.01)
        self.assertEqual(result.status, 'overflow')
        self.assertTrue(math.isinf(result.budget))
        with localcontext() as context:
            context.prec = 90
            # Below saturation, the one-gap formula is
            # Q = (rho + sqrt(rho (1-rho))) / (d sqrt(B)).
            rho = Decimal(1) / 4
            coefficient = (rho + (rho * (1 - rho)).sqrt()) / decimal(gap)
            expected_log = 2 * (coefficient / decimal(0.01)).ln()
            self.assertAlmostEqual(result.log_budget, float(expected_log), delta=8e-13)

    def test_inverse_against_high_precision_monotone_search(self):
        gaps, weights, rho = [0.5, 0.125, 0.03125, 0.00390625], [8, 4, 3, 1], 0.25
        profile = RareEventProfile(FiniteGapLaw(gaps, weights), rho)
        with localcontext() as context:
            context.prec = 90
            atoms = normalized_atoms(gaps, weights)
            tail, core = split(atoms, rho)
            coefficient = (decimal(rho) * gamma(core)).sqrt()
            for target in (0.249, 0.1, 0.03, 0.001):
                low, high = Decimal(0), Decimal(1)
                for _ in range(260):
                    middle = (low + high) / 2
                    value = tail_cost(tail, middle) + coefficient * middle
                    if value <= decimal(target):
                        low = middle
                    else:
                        high = middle
                expected_budget = 1 / high ** 2
                result = profile.budget_for_rate(target)
                with self.subTest(target=target):
                    self.assertEqual(result.status, 'finite')
                    self.assert_decimal_close(result.budget, expected_budget)

    def test_underflowing_positive_normalized_mass_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'underflow'):
            FiniteGapLaw([0.125, 0.5], [math.nextafter(0.0, 1.0), sys.float_info.max])


if __name__ == '__main__':
    unittest.main()
