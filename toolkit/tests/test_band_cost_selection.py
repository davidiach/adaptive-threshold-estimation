"""Check the cost-multiset reduction against all hard selections on small laws."""

from decimal import Decimal, localcontext
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from threshold_toolkit.band_cost_selection import _saves_more, select_by_band_cost
from threshold_toolkit.rare_event_functional import FiniteGapLaw, Precision, band_index


def dec(q):
    return Decimal(q.numerator) / Decimal(q.denominator)


def objective(law, selected, rho, budget):
    costs = {}
    ordinary = Decimal(0)
    for a, keep in zip(law.atoms, selected):
        if keep:
            j = band_index(a.gap)
            costs[j] = costs.get(j, F(0)) + a.mass / a.gap**2
        else:
            ordinary += dec(a.mass) * min(1, 1 / (dec(budget).sqrt() * dec(a.gap)))
    total = sum(costs.values(), F(0))
    entropy = sum(
        (dec(v) * (1 + dec(total / v).ln()) for v in costs.values()), Decimal(0)
    )
    return min(dec(rho), (dec(rho) * entropy / dec(budget)).sqrt() + ordinary)


class BandCostSelectionTests(unittest.TestCase):
    def test_global_value_against_every_subset(self):
        # Two bands have identical suffix costs; both contain multiple atoms.
        gaps = [F(1, 2), F(3, 8), F(1, 4), F(3, 16), F(1, 8)]
        for weights in ([1, 1, 1, 1, 1], [3, 2, 3, 2, 1], [1, 3, 2, 4, 5]):
            m = [d * d * w for w, d in zip(weights, gaps)]
            law = FiniteGapLaw([(d, w / sum(m)) for d, w in zip(gaps, m)])
            for rho, budget in [
                (F(1, 4), F(1)),
                (F(1, 4), F(99, 2)),
                (F(1, 7), F(10007)),
            ]:
                with (
                    self.subTest(weights=weights, budget=budget),
                    localcontext() as ctx,
                ):
                    ctx.prec = 75
                    result = select_by_band_cost(law, rho=rho, budget=budget)
                    brute = min(
                        objective(law, bits, rho, budget)
                        for bits in product((False, True), repeat=len(gaps))
                    )
                    # The independent decimal evaluator rounds at its last place.
                    slack = Decimal("1e-70")
                    self.assertLessEqual(dec(result.value.lower), brute + slack)
                    self.assertGreaterEqual(dec(result.value.upper), brute - slack)
                    self.assertLess(dec(result.value.width), Decimal("1e-20"))
                    self.assertTrue(result.optimality_proved)
                    self.assertLessEqual(
                        abs(objective(law, result.selected, rho, budget) - brute), slack
                    )

    def test_repeated_costs_on_sixty_four_bands(self):
        gaps = [F(1, 2**i) for i in range(1, 65)]
        z = sum(d * d for d in gaps)
        law = FiniteGapLaw([(d, d * d / z) for d in gaps])
        r = select_by_band_cost(law, rho="1/4", budget=2**32, max_transitions=4160)
        self.assertEqual(
            (r.suffix_count, r.final_states, r.transitions), (2**64, 65, 4160)
        )
        self.assertTrue(r.optimality_proved)
        self.assertEqual(
            [a.gap for a, k in zip(law.atoms, r.selected) if k], [F(1, 4), F(1, 2)]
        )
        with self.assertRaisesRegex(ValueError, "max_transitions"):
            select_by_band_cost(law, rho="1/4", budget=2**32, max_transitions=4159)

    def test_near_tie_is_only_certified_after_refinement(self):
        law = FiniteGapLaw([("1/2", 1)])
        budget = 16 + F(1, 10**10)
        low = select_by_band_cost(
            law, rho="1/4", budget=budget, precision=Precision(bits=16)
        )
        high = select_by_band_cost(law, rho="1/4", budget=budget)
        self.assertFalse(low.optimality_proved)
        self.assertTrue(high.optimality_proved)
        self.assertEqual(high.selected, (True,))

    def test_symbolic_order_including_exact_cancellation(self):
        for x, y, b in [(1, -3, 9), (-1, 3, 9), (0, 0, 2)]:
            self.assertFalse(_saves_more(F(x), F(y), F(b)))
        # Adjacent rationals straddle sqrt(2) at 30 decimal places.
        t = F(1414213562373095048801688724209, 10**30)
        self.assertFalse(_saves_more(F(-1), t, F(2)))
        self.assertTrue(_saves_more(F(-1), t + F(1, 10**30), F(2)))
