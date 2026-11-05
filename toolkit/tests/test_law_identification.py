"""Finite exact checks of the observable pilot; these do not prove coverage."""

from dataclasses import replace
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from threshold_toolkit.law_identification import plan_law_pilot, run_law_pilot
from threshold_toolkit.rare_event_functional import FiniteGapLaw


class LawIdentificationTests(unittest.TestCase):
    def test_even_parity_means_and_reflection(self):
        for gap in [F(1, 2), F(1, 4), F(1, 10)]:
            for k in range(1, 4):
                for sign in [-1, 1]:
                    p = F(1, 2) + sign * gap
                    expectation = F(0)
                    for word in product([0, 1], repeat=2*k):
                        score = probability = F(1)
                        reflected = 1
                        for bit in word:
                            score *= 2*bit-1
                            probability *= p if bit else 1-p
                            reflected *= 2*(1-bit)-1
                        self.assertEqual(score, reflected)
                        expectation += probability * score
                    self.assertEqual(expectation, (2*gap)**(2*k))

    def test_higher_moments_separate_equal_second_moments(self):
        point = FiniteGapLaw([("1/4", 1)])
        mixture = FiniteGapLaw([("1/8", "4/5"), ("1/2", "1/5")])
        with self.assertRaises(ValueError):
            plan_law_pilot([point, mixture], delta="1/10", max_moments=1)
        plan = plan_law_pilot([point, mixture], delta="1/10")
        self.assertEqual(plan.moments, 2)
        self.assertEqual(plan.signatures[0][0], plan.signatures[1][0])
        self.assertNotEqual(plan.signatures[0][1], plan.signatures[1][1])
        self.assertEqual(plan.flip_cap, 6*plan.samples_per_moment)

    def test_exact_sampling_bound(self):
        laws = [FiniteGapLaw([("1/2", 1)]), FiniteGapLaw([("1/4", 1)])]
        for delta in [F(1, 4), F(1, 100), F(1, 2**200)]:
            plan = plan_law_pilot(laws, delta=delta)
            rate = plan.samples_per_moment * plan.separation**2 / 32
            exponent = rate.numerator // rate.denominator
            self.assertLessEqual(F(2*plan.moments, 2**exponent), delta)

    def test_paid_execution_and_sign_invariance(self):
        plan = plan_law_pilot([
            FiniteGapLaw([("1/2", 1)]), FiniteGapLaw([("1/4", 1)])
        ], delta="1/4")
        for reflected in [False, True]:
            calls = [0, 0]

            def factory(rng):
                i = calls[0]
                calls[0] += 1
                bits = iter([0, 0 if i % 8 < 5 else 1])

                def flip():
                    calls[1] += 1
                    return next(bits) ^ int(reflected)

                return flip

            out = run_law_pilot(plan, factory, budget=plan.flip_cap)
            self.assertEqual(out.selected, 1)
            self.assertEqual(out.flips, plan.flip_cap)
            self.assertEqual((out.items, out.flips), tuple(calls))
            self.assertLessEqual(abs(out.observed[0]-F(1, 4)), plan.separation/4)

    def test_no_flips_without_authorization_or_with_tampered_plan(self):
        plan = plan_law_pilot([
            FiniteGapLaw([("1/2", 1)]), FiniteGapLaw([("1/4", 1)])
        ], delta="1/4")

        def forbidden(rng):
            self.fail("No coin should be created")

        with self.assertRaises(ValueError):
            run_law_pilot(plan, forbidden, budget=plan.flip_cap-1)
        with self.assertRaises(ValueError):
            run_law_pilot(replace(plan, samples_per_moment=1), forbidden,
                          budget=plan.flip_cap)

    def test_singleton_and_duplicate_laws(self):
        law = FiniteGapLaw([("1/2", 1)])
        plan = plan_law_pilot([law], delta="1/4")
        out = run_law_pilot(plan, lambda _: self.fail("No coin is needed"), budget=0)
        self.assertEqual((out.selected, out.flips, out.items), (0, 0, 0))
        duplicate = FiniteGapLaw([("1/2", "1/3"), ("1/2", "2/3")])
        with self.assertRaises(ValueError):
            plan_law_pilot([law, duplicate], delta="1/4")

    def test_invalid_parameters_and_observations(self):
        laws = [FiniteGapLaw([("1/2", 1)]), FiniteGapLaw([("1/4", 1)])]
        for delta in [0, 1, -1]:
            with self.assertRaises(ValueError):
                plan_law_pilot(laws, delta=delta)
        for limit in [0, -1, True]:
            with self.assertRaises(ValueError):
                plan_law_pilot(laws, delta="1/4", max_moments=limit)
        with self.assertRaises(ValueError):
            plan_law_pilot([], delta="1/4")
        plan = plan_law_pilot(laws, delta="1/4")
        with self.assertRaises(ValueError):
            run_law_pilot(plan, lambda _: lambda: 2, budget=plan.flip_cap)


if __name__ == "__main__":
    unittest.main()

