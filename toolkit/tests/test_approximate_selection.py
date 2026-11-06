"""Independent subset enumeration and adversarial cases for state trimming."""

from decimal import Decimal, localcontext
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from random import Random
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from threshold_toolkit.approximate_selection import (
    _bin, _upper_log, select_approximately,
)
from threshold_toolkit.band_cost_selection import select_by_band_cost
from threshold_toolkit.rare_event_functional import (
    FiniteGapLaw, Precision, evaluate_selection,
)


def dec(x):
    return Decimal(x.numerator) / Decimal(x.denominator)


def direct_objective(law, selected, rho, budget):
    # Deliberately independent band assignment and transcendental evaluation.
    costs = {}
    tail = Decimal(0)
    for atom, keep in zip(law.atoms, selected):
        if keep:
            band, top = 0, F(1, 2)
            while atom.gap <= top / 2:
                band, top = band + 1, top / 2
            costs[band] = costs.get(band, F(0)) + atom.mass / atom.gap**2
        else:
            tail += dec(atom.mass) * min(1, 1 / (dec(atom.gap) * dec(budget).sqrt()))
    total = sum(costs.values(), F(0))
    entropy = sum((dec(a) * (1 + dec(total / a).ln()) for a in costs.values()), Decimal(0))
    return min(dec(rho), tail + (dec(rho) * entropy / dec(budget)).sqrt())


class ApproximateSelectionTests(unittest.TestCase):
    def assert_matches_all_subsets(self, law, rho, budget, epsilon):
        result = select_approximately(law, rho=rho, budget=budget, epsilon=epsilon)
        with localcontext() as ctx:
            ctx.prec = 90
            optimum = min(direct_objective(law, bits, rho, budget)
                          for bits in product((False, True), repeat=len(law.atoms)))
            witness = direct_objective(law, result.selected, rho, budget)
            slack = max(abs(optimum), Decimal("1e-200")) * Decimal("1e-75")
            self.assertLessEqual(dec(result.value.lower), optimum + slack)
            self.assertLessEqual(witness, dec(result.value.upper) + slack)
            self.assertLessEqual(witness, (1 + dec(epsilon)) * optimum + slack)
        self.assertLessEqual(result.value.upper, (1 + epsilon) * result.value.lower)
        reevaluated = evaluate_selection(law, tuple(map(int, result.selected)),
                                        rho=rho, budget=budget, precision=result.precision)
        self.assertEqual(result.witness_value, reevaluated)
        return result

    def test_random_small_laws_against_every_subset(self):
        rng = Random(20261106)
        gaps = [F(1, 2), F(3, 8), F(1, 4), F(3, 16), F(1, 8), F(1, 32), F(1, 1024)]
        for trial in range(24):
            support = rng.sample(gaps, rng.randint(2, 7))
            masses = [rng.randint(1, 30) for _ in support]
            law = FiniteGapLaw([(d, F(w, sum(masses))) for d, w in zip(support, masses)])
            with self.subTest(trial=trial):
                self.assert_matches_all_subsets(
                    law, F(1, rng.choice([4, 7, 1000])),
                    F(rng.choice([1, 17, 10000, 10**12]), rng.choice([1, 3])),
                    rng.choice([F(1), F(1, 2), F(1, 10)]),
                )

    def test_point_laws_saturation_and_tiny_values(self):
        for gap in [F(1, 2), F(1, 10000)]:
            law = FiniteGapLaw([(gap, 1)])
            for rho, budget in [(F(1, 4), F(1, 10)), (F(1, 4), F(16)),
                                (F(1, 10**30), F(10**100))]:
                with self.subTest(gap=gap, rho=rho, budget=budget):
                    self.assert_matches_all_subsets(law, rho, budget, F(1, 10))

    def test_many_distinct_costs_actually_compress(self):
        gaps = [F(1, 2**i) for i in range(1, 41)]
        masses = [d*d*(1+F(i, 10**12)) for i, d in enumerate(gaps)]
        total = sum(masses)
        law = FiniteGapLaw([(d, w/total) for d, w in zip(gaps, masses)])
        self.assertEqual(len({a.mass/a.gap**2 for a in law.atoms}), 40)
        result = select_approximately(law, rho="1/4", budget=2**32,
                                      epsilon="1/10", max_transitions=5000)
        self.assertEqual(result.suffix_count, 2**40)
        self.assertLess(result.final_states, 100)
        self.assertLess(result.transitions, 5000)
        with self.assertRaisesRegex(ValueError, "max_transitions"):
            select_by_band_cost(law, rho="1/4", budget=2**32, max_transitions=5000)

    def test_near_equal_costs_against_all_subsets(self):
        gaps = [F(1, 2**i) for i in range(1, 9)]
        raw = [d*d*(1+F(i, 10**10)) for i, d in enumerate(gaps)]
        law = FiniteGapLaw([(d, w/sum(raw)) for d, w in zip(gaps, raw)])
        result = self.assert_matches_all_subsets(law, F(1, 4), F(2**20), F(1, 10))
        self.assertLess(result.final_states, result.suffix_count)

    def test_bins_handle_exact_boundaries_and_zero(self):
        r, m = F(3, 7), 13
        self.assertEqual(_bin(F(0), r, m), (-1, -1))
        for k in range(6):
            for j in range(m):
                lower = r*2**k*(1+F(j, m))
                upper = r*2**k*(1+F(j+1, m))
                self.assertEqual(_bin(lower, r, m), (k, j))
                self.assertEqual(_bin((lower+upper)/2, r, m), (k, j))
                self.assertNotEqual(_bin(upper, r, m), (k, j))
                self.assertLessEqual(upper/lower, 1+F(1, m))

    def test_log_surrogates_near_one_and_large(self):
        with localcontext() as ctx:
            ctx.prec = 90
            for x in [F(1), 1+F(1, 10**40), F(3, 2), F(2**400)]:
                for epsilon in [F(1), F(1, 10**12)]:
                    u = _upper_log(x, epsilon)
                    actual = dec(x).ln()
                    self.assertGreaterEqual(dec(u)+Decimal("1e-85"), actual)
                    self.assertLessEqual(dec(u)-actual, dec(epsilon)/8+Decimal("1e-85"))

    def test_final_precision_refines(self):
        law = FiniteGapLaw([("1/2", 1)])
        result = select_approximately(law, rho="1/4", budget=17,
                                      epsilon="1/1000000000000",
                                      precision=Precision(bits=16, log_terms=4))
        self.assertGreater(result.precision.bits, 16)
        self.assertLessEqual(result.value.upper, (1+result.epsilon)*result.value.lower)

    def test_bad_inputs_and_resource_failure(self):
        law = FiniteGapLaw([("1/2", "1/2"), ("1/4", "1/2")])
        for epsilon in [0, -1, 2]:
            with self.assertRaises(ValueError):
                select_approximately(law, rho="1/4", budget=10, epsilon=epsilon)
        for epsilon in [0.1, True]:
            with self.assertRaises(TypeError):
                select_approximately(law, rho="1/4", budget=10, epsilon=epsilon)
        for limit in [0, True, 1.5]:
            with self.assertRaises(ValueError):
                select_approximately(law, rho="1/4", budget=10, max_transitions=limit)
        with self.assertRaisesRegex(ValueError, "max_transitions"):
            select_approximately(law, rho="1/4", budget=10, max_transitions=1)


if __name__ == "__main__":
    unittest.main()
