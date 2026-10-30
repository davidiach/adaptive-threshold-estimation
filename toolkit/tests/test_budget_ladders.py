from __future__ import annotations
import copy
from decimal import Decimal, localcontext
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import random
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from threshold_toolkit.budget_ladders import (
    stage, plan, schedule_record, verify_schedule, RMSLadder,
)

def zero_coin(rng):
    return lambda: 0


def mean_program(b, rng):
    total = 0
    for i in range(b):
        total += yield i
    return F(total, b)


def immediate(value):
    def factory(b, rng):
        if False:
            yield 0
        return value
    return factory


class ScheduleTests(unittest.TestCase):
    def test_checkpoints(self):
        self.assertEqual([stage(j).checkpoint for j in range(5)], [4,12,28,60,124])
        self.assertEqual([stage(j).flip_cap for j in range(5)], [4,8,16,32,64])

    def test_small_budgets(self):
        for n in range(4):
            self.assertEqual(plan(n), ())

    def test_all_budgets(self):
        for n in range(2001):
            p = plan(n)
            self.assertLessEqual(sum(s.flip_cap for s in p), n)
            self.assertGreater(stage(len(p)).checkpoint, n)
            if p:
                self.assertGreater(p[-1].flip_cap, F(n,4))

    def test_large_plan_no_execution(self):
        n = 10**300
        p = plan(n)
        self.assertLess(len(p), 1000)
        self.assertLessEqual(sum(s.flip_cap for s in p), n)

    def test_maximum_budget_bit_boundary(self):
        n=(1<<4096)-1
        p=plan(n)
        self.assertEqual(p[-1].index,4093)
        self.assertLessEqual(sum(s.flip_cap for s in p),n)

    def test_invalid_budget(self):
        for n in [-1, True, 2.0, '4', None]:
            with self.assertRaises((TypeError,ValueError)):
                plan(n)

    def test_invalid_stage(self):
        for n in [-1, True, 0.0, 5000]:
            with self.assertRaises(ValueError):
                stage(n)

    def test_replay(self):
        self.assertTrue(verify_schedule(schedule_record(1000), total_budget=1000))
        self.assertFalse(verify_schedule(schedule_record(1000), total_budget=999))

    def test_corruption_rejection(self):
        rec = schedule_record(1000)
        for key in rec:
            bad = copy.deepcopy(rec)
            del bad[key]
            self.assertFalse(verify_schedule(bad, total_budget=1000))
        bad = copy.deepcopy(rec)
        bad['caps'][0] = True
        self.assertFalse(verify_schedule(bad, total_budget=1000))
        bad = dict(rec, extra=1)
        self.assertFalse(verify_schedule(bad, total_budget=1000))


class RMSTests(unittest.TestCase):
    def test_fallback(self):
        r = RMSLadder(mean_program, zero_coin, upper='1/4').advance_to(3)
        self.assertEqual((r.estimate,r.flips,r.reserved_budget), (F(1,8),0,0))

    def test_complete(self):
        r = RMSLadder(mean_program, zero_coin).advance_to(28)
        self.assertEqual(r.estimate, 0)
        self.assertEqual(r.flips, 7)
        self.assertEqual(r.reserved_budget,28)

    def test_retains_previous_on_timeout(self):
        def factory(b,rng):
            if b == 1:
                if False: yield 0
                return F(1,10)
            while True:
                yield 0
        r = RMSLadder(factory,zero_coin,upper='1/4').advance_to(60)
        self.assertEqual(r.estimate,F(1,10))
        self.assertEqual(sum(x.timed_out for x in r.runs),3)
        self.assertEqual(r.flips,56)

    def test_finishes_at_cap(self):
        def factory(b,rng):
            for _ in range(4*b): yield 0
            return F(1,7)
        r = RMSLadder(factory,zero_coin).advance_to(60)
        self.assertEqual(r.flips,60)
        self.assertTrue(all(not x.timed_out for x in r.runs))

    def test_request_beyond_cap_not_purchased(self):
        calls = []
        def coins(rng):
            def flip():
                calls.append(1)
                return 0
            return flip
        def factory(b,rng):
            for i in range(4*b+1): yield i
            return 0
        r = RMSLadder(factory,coins).advance_to(28)
        self.assertEqual(len(calls),28)
        self.assertEqual(r.flips,28)
        self.assertEqual(sum(x.created_coins for x in r.runs),28)
        self.assertTrue(all(x.timed_out for x in r.runs))

    def test_persistent_revisits_separate_stages(self):
        made=[]
        def coins(rng):
            i=len(made); made.append(0)
            def flip():
                made[i]+=1
                return 0
            return flip
        def factory(b,rng):
            yield 42; yield 42; yield 9
            return 0
        r=RMSLadder(factory,coins).advance_to(28)
        self.assertEqual(made,[2,1,2,1,2,1])
        self.assertEqual(r.flips,9)

    def test_budget_extension_same_path(self):
        def coins(rng):
            theta=rng.random()
            return lambda: int(rng.random()<theta)
        once=RMSLadder(mean_program,coins,seed=72).advance_to(1000)
        other=RMSLadder(mean_program,coins,seed=72)
        for n in [0,3,4,8,12,27,28,124,1000]: out=other.advance_to(n)
        self.assertEqual(once,out)

    def test_repeat_no_extra_work(self):
        x=RMSLadder(mean_program,zero_coin)
        self.assertEqual(x.advance_to(28),x.advance_to(28))
        with self.assertRaises(ValueError): x.advance_to(27)

    def test_clip(self):
        for v,want in [(-9,0),(8,F(1,4)),(F(1,7),F(1,7))]:
            x=RMSLadder(immediate(v),zero_coin,upper='1/4').advance_to(4)
            self.assertEqual(x.estimate,want)

    def test_invalid_output(self):
        for v in [True, '3/4', None, float('nan'),float('inf')]:
            x=RMSLadder(immediate(v),zero_coin)
            with self.assertRaises((ValueError,TypeError)): x.advance_to(4)
            with self.assertRaises(RuntimeError): x.advance_to(12)

    def test_invalid_ids(self):
        for v in [-1,True,0.0,'0']:
            def factory(b,rng):
                yield v
                return 0
            with self.assertRaises(ValueError): RMSLadder(factory,zero_coin).advance_to(4)

    def test_invalid_bits(self):
        for v in [True,0.0,2,None]:
            with self.assertRaises(ValueError):
                RMSLadder(mean_program,lambda rng: lambda: v).advance_to(4)

    def test_invalid_factory(self):
        with self.assertRaises(TypeError):
            RMSLadder(lambda b,rng: 0,zero_coin).advance_to(4)
        with self.assertRaises(TypeError):
            RMSLadder(mean_program,lambda rng: 0).advance_to(4)

    def test_finalizer_runs(self):
        closed=[]
        def factory(b,rng):
            try:
                while True: yield 0
            finally: closed.append(b)
        RMSLadder(factory,zero_coin).advance_to(28)
        self.assertEqual(closed,[1,2,4])

    def test_constructor_inputs(self):
        for upper in [0,2,False,.25]:
            with self.assertRaises((TypeError,ValueError)):
                RMSLadder(mean_program,zero_coin,upper=upper)
        with self.assertRaises(TypeError): RMSLadder(mean_program,zero_coin,seed=True)

if __name__ == '__main__':
    unittest.main()
