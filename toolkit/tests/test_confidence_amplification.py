"""Tests control flow and exact scheduling; not a proof of statistical minimaxity."""
from __future__ import annotations
from fractions import Fraction as F
import math
import json
import random
import unittest

from threshold_toolkit.confidence_amplification import (
    MedianSchedule, median_block_count, run_capped_median, verify_schedule_record,
)


def constant_program(value):
    def make(budget, rng):
        if False:
            yield 0
        return value
    return make


def fixed_program(count, value=F(1, 10)):
    def make(budget, rng):
        for i in range(count):
            yield i
        return value
    return make


def zero_coin(rng):
    return lambda: 0


class ScheduleTests(unittest.TestCase):
    def test_exact_failure_bound_and_minimality(self):
        for delta in [F(1, 4), F(1, 10), F(1, 100), F(1, 10**20), F(1, 10**300)]:
            m = median_block_count(delta)
            self.assertEqual(m % 2, 1)
            self.assertLessEqual(F(3, 4)**m, delta**2)
            if m > 1:
                self.assertGreater(F(3, 4)**(m-2), delta**2)

    def test_binomial_tail_below_exact_chernoff_bound(self):
        for m in range(1, 80, 2):
            numerator = sum(math.comb(m, k) * 3**(m-k) for k in range(m//2+1, m+1))
            failure = F(numerator, 4**m)
            self.assertLessEqual(failure**2, F(3, 4)**m)

    def test_budget_floor_and_base_budget(self):
        s = MedianSchedule(1000, rho="1/8", delta="1/100")
        self.assertEqual(s.base_expected_budget, F(1000, 8*s.blocks))
        self.assertEqual(s.per_block_cap, 1000//s.blocks)
        self.assertLessEqual(s.deterministic_flip_cap, 1000)

    def test_tiny_budget_has_zero_query_blocks(self):
        s = MedianSchedule(1, rho="1/8", delta="1/100")
        self.assertEqual(s.per_block_cap, 0)
        self.assertGreater(s.base_expected_budget, 0)

    def test_delta_monotonicity(self):
        counts = [median_block_count(F(1, 2**i)) for i in range(2, 30)]
        self.assertEqual(counts, sorted(counts))

    def test_explicit_state_cap(self):
        with self.assertRaises(ValueError):
            median_block_count("1e-100", max_blocks=5)
        m = median_block_count("1/100")
        self.assertEqual(median_block_count("1/100", max_blocks=m), m)
        with self.assertRaises(ValueError):
            median_block_count("1/100", max_blocks=m-1)

    def test_reject_invalid_delta(self):
        for value in ["0", "-1", "1/3", "NaN", "infinity"]:
            with self.assertRaises(ValueError):
                median_block_count(value)
        for value in [0.01, True, None]:
            with self.assertRaises(TypeError):
                median_block_count(value)

    def test_reject_invalid_budget_and_rho(self):
        for value in [0, -1, True, 5.0, "5"]:
            with self.assertRaises(ValueError):
                MedianSchedule(value, rho="1/8", delta="1/100")
        for value in ["0", "-1", "1/2"]:
            with self.assertRaises(ValueError):
                MedianSchedule(10, rho=value, delta="1/100")

    def test_round_trip_instance_bound(self):
        s = MedianSchedule(1000, rho="1/8", delta="1/100")
        self.assertTrue(verify_schedule_record(s.record(), total_budget=1000,
                                              rho="1/8", delta="1/100"))
        self.assertFalse(verify_schedule_record(s.record(), total_budget=999,
                                               rho="1/8", delta="1/100"))
        self.assertFalse(verify_schedule_record(s.record(), total_budget=1000,
                                               rho="1/9", delta="1/100"))
        self.assertFalse(verify_schedule_record(s.record(), total_budget=1000,
                                               rho="1/8", delta="1/99"))

    def test_corruption_rejection(self):
        s = MedianSchedule(1000, rho="1/8", delta="1/100")
        for key in s.record():
            record = s.record()
            record[key] = "corrupted"
            self.assertFalse(verify_schedule_record(record, total_budget=1000,
                                                   rho="1/8", delta="1/100"), key)
        record = s.record()
        record["verified_statistical_risk"] = True
        self.assertFalse(verify_schedule_record(record, total_budget=1000,
                                               rho="1/8", delta="1/100"))

    def test_extreme_delta_record_avoids_giant_power_decimal_encoding(self):
        s = MedianSchedule(100, rho="1/8", delta="1e-1000")
        encoded = json.dumps(s.record())
        self.assertLess(len(encoded), 2000)
        self.assertTrue(verify_schedule_record(s.record(), total_budget=100,
                                              rho="1/8", delta="1e-1000"))

    def test_frozen_schedule(self):
        s = MedianSchedule(1000, rho="1/8", delta="1/100")
        with self.assertRaises(AttributeError):
            s.blocks = 1


class DriverTests(unittest.TestCase):
    def setUp(self):
        self.schedule = MedianSchedule(1000, rho="1/4", delta="1/100")

    def test_immediate_output_without_any_flip(self):
        def forbidden(rng):
            raise AssertionError("No source call permitted")
        result = run_capped_median(self.schedule, constant_program(F(1, 9)), forbidden)
        self.assertEqual(result.estimate, F(1, 9))
        self.assertEqual(result.flips, 0)
        self.assertEqual(result.created_coins, 0)
        self.assertEqual(result.completed_blocks, self.schedule.blocks)

    def test_exact_completion_at_the_cap(self):
        result = run_capped_median(self.schedule, fixed_program(self.schedule.per_block_cap), zero_coin)
        self.assertEqual(result.flips, self.schedule.deterministic_flip_cap)
        self.assertEqual(result.timed_out_blocks, 0)
        self.assertEqual(result.estimate, F(1, 10))

    def test_timeout_never_buys_the_next_observation(self):
        calls = []
        def source(rng):
            def flip():
                calls.append(1)
                return 0
            return flip
        result = run_capped_median(self.schedule, fixed_program(self.schedule.per_block_cap+1), source)
        self.assertEqual(result.flips, self.schedule.deterministic_flip_cap)
        self.assertEqual(len(calls), result.flips)
        self.assertEqual(result.timed_out_blocks, self.schedule.blocks)
        self.assertEqual(result.estimate, self.schedule.rho/2)

    def test_infinite_flip_program_is_truncated(self):
        def infinite(budget, rng):
            while True:
                yield 0
        result = run_capped_median(self.schedule, infinite, zero_coin)
        self.assertEqual(result.flips, self.schedule.deterministic_flip_cap)
        self.assertEqual(result.timed_out_blocks, self.schedule.blocks)
        self.assertEqual(result.created_coins, self.schedule.blocks)

    def test_zero_cap_does_not_create_or_flip_coin(self):
        s = MedianSchedule(1, rho="1/8", delta="1/100")
        def forbidden(rng):
            raise AssertionError("No source call permitted")
        result = run_capped_median(s, fixed_program(1), forbidden)
        self.assertEqual(result.flips, 0)
        self.assertEqual(result.created_coins, 0)
        self.assertEqual(result.timed_out_blocks, s.blocks)

    def test_revisits_keep_latent_state_and_local_history(self):
        def source(rng):
            count = 0
            def flip():
                nonlocal count
                count += 1
                return count % 2
            return flip
        def program(budget, rng):
            a = yield 17
            b = yield 17
            c = yield 90210
            self.assertEqual((a, b, c), (1, 0, 1))
            return F(1, 10)
        result = run_capped_median(self.schedule, program, source)
        self.assertEqual(result.created_coins, 2*self.schedule.blocks)
        self.assertEqual(result.flips, 3*self.schedule.blocks)

    def test_interleaving_supported(self):
        def source(rng):
            count = 0
            def flip():
                nonlocal count
                count += 1
                return count % 2
            return flip
        def program(budget, rng):
            observed = []
            for label in (0, 1, 0, 1, 0, 1):
                observed.append((yield label))
            self.assertEqual(observed, [1, 1, 0, 0, 1, 1])
            return F(1, 10)
        result = run_capped_median(self.schedule, program, source)
        self.assertEqual(result.flips, 6*self.schedule.blocks)

    def test_clip_does_not_round_rational_outputs(self):
        tiny = F(1, 10**500)
        result = run_capped_median(self.schedule, constant_program(tiny), zero_coin)
        self.assertEqual(result.estimate, tiny)
        for value, expected in [(-2, 0), (10**1000, F(1, 4))]:
            result = run_capped_median(self.schedule, constant_program(value), zero_coin)
            self.assertEqual(result.estimate, expected)

    def test_reject_nonfinite_output_not_silently_clip(self):
        for value in [math.inf, -math.inf, math.nan]:
            with self.assertRaises(ValueError):
                run_capped_median(self.schedule, constant_program(value), zero_coin)

    def test_reject_invalid_output_type(self):
        for value in [None, "0.1", True]:
            with self.assertRaises(TypeError):
                run_capped_median(self.schedule, constant_program(value), zero_coin)

    def test_reject_invalid_coin_id(self):
        for label in [True, -1, "0", 0.0]:
            def invalid(budget, rng):
                yield label
                return F(1, 10)
            with self.assertRaises(ValueError):
                run_capped_median(self.schedule, invalid, zero_coin)

    def test_reject_invalid_source_output(self):
        for bit in [True, -1, 2, "0", 0.0]:
            with self.assertRaises(ValueError):
                run_capped_median(self.schedule, fixed_program(1), lambda rng: lambda: bit)

    def test_factory_error_propagates(self):
        def broken(rng):
            raise RuntimeError("source failed")
        with self.assertRaisesRegex(RuntimeError, "source failed"):
            run_capped_median(self.schedule, fixed_program(1), broken)

    def test_generator_closed_on_timeout(self):
        closed = []
        def program(budget, rng):
            try:
                while True:
                    yield 0
            finally:
                closed.append(True)
        run_capped_median(self.schedule, program, zero_coin)
        self.assertEqual(len(closed), self.schedule.blocks)

    def test_program_and_source_randomness_separated(self):
        program_rngs, source_rngs = [], []
        def program(budget, rng):
            program_rngs.append(rng)
            yield 0
            return F(1, 10)
        def source(rng):
            source_rngs.append(rng)
            return lambda: 0
        run_capped_median(self.schedule, program, source)
        self.assertTrue(set(map(id, program_rngs)).isdisjoint(map(id, source_rngs)))
        self.assertEqual(len(set(map(id, source_rngs))), self.schedule.blocks)

    def test_seed_reproducibility(self):
        def source(rng):
            p = F(1, 8) if rng.randrange(2) else F(7, 8)
            return lambda: int(rng.random() < p)
        def program(budget, rng):
            total = 0
            for k in range(10):
                total += yield k//2
            return F(total, 40)
        first = run_capped_median(self.schedule, program, source, seed=42)
        second = run_capped_median(self.schedule, program, source, seed=42)
        self.assertEqual(first, second)

    def test_budget_randomized_control_flow_regression(self):
        for seed in range(100):
            s = MedianSchedule(seed+1, rho="1/4", delta="1/10")
            def program(budget, rng):
                for i in range(rng.randrange(20)):
                    yield rng.randrange(4)
                return F(1, 10)
            result = run_capped_median(s, program, zero_coin, seed=seed)
            self.assertLessEqual(result.flips, s.total_budget)
            self.assertEqual(result.flips, sum(result.per_block_flips))
            self.assertTrue(all(n <= s.per_block_cap for n in result.per_block_flips))


if __name__ == "__main__":
    unittest.main()
