"""Exact finite checks and controller regressions, not a proof for all laws."""

from dataclasses import replace
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from threshold_toolkit.tail_mass import TailMassProbe, plan_tail_mass, run_tail_mass


def exact_coin_law(depth, p):
    """Independent finite DP using integer probability numerators.

    Retain only prefixes not resolved at earlier checks, paying for the next
    flip on exactly those prefixes. No random simulations or floats enter.
    """
    denominator = p.denominator
    heads_weight = p.numerator
    tails_weight = denominator - heads_weight
    alive = [1]
    scale = 1
    work = F(0)
    for n in range(1, 4**depth + 1):
        work += F(sum(alive), scale)
        following = [0] * (n + 1)
        for heads, weight in enumerate(alive):
            following[heads] += weight * tails_weight
            following[heads + 1] += weight * heads_weight
        scale *= denominator
        if n & (n - 1) == 0 and (n.bit_length() - 1) % 2 == 0:
            level = (n.bit_length() - 1) // 2
            square = 2 * n * (depth - level + 2)
            threshold = isqrt(square)
            if threshold**2 < square:
                threshold += 1
            following = [weight if abs(2 * h - n) <= 2 * threshold else 0
                         for h, weight in enumerate(following)]
        alive = following
    return work, F(sum(alive), scale)


class TailMassTests(unittest.TestCase):
    def scripted(self, reflected=False):
        counts = []

        def factory(rng):
            index = len(counts)
            counts.append(0)

            def flip():
                prefix = counts[index]
                counts[index] += 1
                # Two resolved coins, followed by a terminal unresolved one.
                bit = int(index == 1) if index < 2 else prefix % 2
                return bit ^ int(reflected)

            return flip

        return factory, counts

    def test_every_pause_preserves_coin_and_matches_one_shot(self):
        factory, counts = self.scripted()
        direct = TailMassProbe(4, factory).advance_to(1000)
        self.assertEqual((direct.completed, direct.unresolved), (3, True))
        self.assertEqual(counts, [64, 64, 256])
        for split in range(direct.flips + 1):
            factory, counts = self.scripted()
            probe = TailMassProbe(4, factory)
            first = probe.advance_to(split)
            self.assertLessEqual(first.flips, split)
            self.assertEqual(first.flips, sum(counts))
            self.assertEqual(probe.advance_to(split), first)
            final = probe.advance_to(1000)
            self.assertEqual(final, direct)
            self.assertEqual(sum(counts), final.flips)

    def test_complementing_flips_preserves_all_states(self):
        original, count_a = self.scripted()
        reflected, count_b = self.scripted(True)
        a, b = TailMassProbe(4, original), TailMassProbe(4, reflected)
        for budget in range(401):
            self.assertEqual(a.advance_to(budget), b.advance_to(budget))
        self.assertEqual(count_a, count_b)

    def test_unfinished_coin_is_charged_but_not_completed(self):
        factory, counts = self.scripted()
        probe = TailMassProbe(4, factory)
        state = probe.advance_to(127)
        self.assertEqual((state.flips, state.items, state.completed), (127, 2, 1))
        self.assertEqual(counts, [64, 63])
        self.assertEqual(state.upper, 1)
        self.assertEqual(probe.advance_to(128).completed, 2)

    def test_terminal_equality_stays_unresolved(self):
        # At depth 4 the final count threshold is exactly 32. A path with
        # 160 heads has excess 64 and must not be declared resolved.
        bits = iter([0, 1] * 64 + [1, 1, 1, 0] * 32)
        state = TailMassProbe(4, lambda _: lambda: next(bits)).advance_to(256)
        self.assertTrue(state.unresolved)
        self.assertEqual((state.flips, state.completed), (256, 1))

    def test_no_coin_without_authorization_and_monotone_budgets(self):
        probe = TailMassProbe(4, lambda _: self.fail("Unexpected coin"))
        self.assertEqual(probe.advance_to(0).items, 0)
        for invalid in [-1, True, F(1), 0.5]:
            with self.assertRaises((ValueError, TypeError)):
                probe.advance_to(invalid)
        probe = TailMassProbe(4, lambda _: lambda: 0)
        probe.advance_to(1)
        with self.assertRaises(ValueError):
            probe.advance_to(0)

    def test_failed_callback_invalidates_even_at_same_budget(self):
        for invalid in [True, 2, F(0)]:
            probe = TailMassProbe(4, lambda _, bit=invalid: lambda: bit)
            with self.assertRaises(ValueError):
                probe.advance_to(1)
            with self.assertRaises(RuntimeError):
                probe.advance_to(1)
        probe = TailMassProbe(4, lambda _: None)
        with self.assertRaises(TypeError):
            probe.advance_to(1)
        with self.assertRaises(RuntimeError):
            probe.advance_to(1)
        calls = []

        def failed_flip():
            calls.append(1)
            raise OSError("instrument failure")

        probe = TailMassProbe(4, lambda _: failed_flip)
        with self.assertRaises(OSError):
            probe.advance_to(10)
        self.assertEqual(len(calls), 1)
        self.assertEqual(probe._flips, 1)
        with self.assertRaises(RuntimeError):
            probe.advance_to(10)

    def test_plan_calibration_is_exact_even_for_tiny_delta(self):
        for delta in [F(1, 2), F(1, 20), F(1, 2**300)]:
            plan = plan_tail_mass(3, delta=delta)
            exponent = (plan.blocks - 1) // 8
            self.assertLessEqual(F(2, 2**exponent), delta)
            self.assertEqual(plan.blocks % 2, 1)
            self.assertEqual(plan.scale, F(1, 8))
            self.assertEqual(plan.flip_cap, 64 * plan.blocks)

    def test_plan_rejects_invalid_inputs_before_acquisition(self):
        for depth in [0, -1, True, 1.5]:
            with self.assertRaises(ValueError):
                plan_tail_mass(depth, delta="1/20")
        for delta in [0, 1, -1, True, 0.1]:
            with self.assertRaises((ValueError, TypeError)):
                plan_tail_mass(4, delta=delta)
        plan = plan_tail_mass(4, delta="1/20")
        factory = lambda _: self.fail("Unexpected coin")
        with self.assertRaises(ValueError):
            run_tail_mass(plan, factory, budget=plan.flip_cap - 1)
        with self.assertRaises(ValueError):
            run_tail_mass(replace(plan, blocks=1), factory, budget=plan.flip_cap)
        with self.assertRaises(TypeError):
            run_tail_mass(plan, factory, budget=plan.flip_cap, seed=True)

    def test_actual_nonvacuous_median_and_flip_counts(self):
        calls = [0, 0]

        def factory(rng):
            calls[0] += 1
            bit = rng.randrange(2)

            def flip():
                calls[1] += 1
                return bit

            return flip

        plan = plan_tail_mass(6, delta="1/20")
        result = run_tail_mass(plan, factory, budget=plan.flip_cap, seed=19)
        # Each deterministic coin resolves after 64 flips; 64 fit per block.
        self.assertEqual(result.upper, F(1, 8))
        self.assertEqual((result.items, result.flips), tuple(calls))
        self.assertEqual(result.flips, plan.flip_cap)
        self.assertTrue(all(s.completed == 64 and not s.unresolved for s in result.blocks))

    def test_median_uses_distinct_fresh_streams_and_first_unresolved_stop(self):
        calls = [0, 0]

        def factory(rng):
            calls[0] += 1
            prefix = [0]

            def flip():
                calls[1] += 1
                prefix[0] += 1
                return prefix[0] % 2

            return flip

        plan = plan_tail_mass(4, delta="1/4")
        result = run_tail_mass(plan, factory, budget=plan.flip_cap)
        self.assertEqual(result.upper, 1)
        self.assertEqual(result.items, plan.blocks)
        self.assertEqual(result.flips, plan.flip_cap)
        self.assertTrue(all(s.completed == 1 and s.unresolved for s in result.blocks))

    def test_exact_conditional_retention_and_reflection(self):
        for depth in range(1, 5):
            scale = F(1, 2**depth)
            work, unresolved = exact_coin_law(depth, F(1, 2) + scale)
            self.assertGreaterEqual(unresolved, F(1, 2))
            self.assertLessEqual(work, 4**depth)
            self.assertEqual((work, unresolved), exact_coin_law(depth, F(1, 2) - scale))

    def test_exact_conditional_large_gap_envelope(self):
        # Depth 4 has a nontrivial bound for d > 1/4; include terminal and
        # earlier-resolution contributions in the exact rational DP.
        for p in [F(0), F(1, 16), F(1, 8), F(3, 16)]:
            work, unresolved = exact_coin_law(4, p)
            gap = abs(p - F(1, 2))
            self.assertLessEqual(unresolved, min(F(1), 16 / (256 * gap**2)))
            self.assertLessEqual(work, 256)
        self.assertEqual(exact_coin_law(4, F(0)), (F(64), F(0)))

    def test_inverse_sampling_failure_bound_exactly(self):
        # First-success sampling, including a completed unresolved coin.
        # The all-budget bad event needs floor(4/u) consecutive failures.
        for numerator in range(1, 65):
            u = F(numerator, 64)
            exponent = 4 // u
            self.assertLessEqual((1 - u)**exponent, F(1, 8))


if __name__ == "__main__":
    unittest.main()
