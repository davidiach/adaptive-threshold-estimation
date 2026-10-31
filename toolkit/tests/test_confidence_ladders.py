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
from threshold_toolkit.confidence_ladders import (
    stage, stage_delta, ConfidenceLadder, ClosedInterval, bernoulli_interval,
    _log_upper, _sqrt_upper,
)

def zero_coin(rng):
    return lambda: 0


def full_interval(cap, delta, rng):
    if False:
        yield 0
    return ClosedInterval(0, 1)


class FailureScheduleTests(unittest.TestCase):
    def test_failure_schedule_exact(self):
        d = F(1,100)
        for m in range(40):
            spent = sum(stage_delta(d,j) for j in range(m+1))
            self.assertEqual(spent, d*F(m+1,m+2))

    def test_tiny_delta(self):
        d = F(1, 10**1000)
        self.assertEqual(stage_delta(d,9), d/110)

    def test_invalid_delta(self):
        for d in [0, '-1/10', '1/2', True, .01, 'nan']:
            with self.assertRaises((TypeError,ValueError)):
                stage_delta(d, 0)


class ConfidenceTests(unittest.TestCase):
    def test_initial_and_spending(self):
        x=ConfidenceLadder(full_interval,zero_coin,delta='1/20',upper='1/4')
        a=x.advance_to(3)
        self.assertEqual(a.interval,ClosedInterval(0,F(1,4)))
        self.assertEqual(a.spent_failure_budget,0)
        b=x.advance_to(28)
        self.assertEqual(b.spent_failure_budget,F(3,80))
        self.assertEqual(b.remaining_failure_budget,F(1,80))

    def test_intersection(self):
        def factory(cap,d,rng):
            if False: yield 0
            return {4:ClosedInterval('1/10','1/4'),8:ClosedInterval('1/20','1/5'),
                    16:ClosedInterval('3/20','1/3')}[cap]
        r=ConfidenceLadder(factory,zero_coin,delta='1/20',upper='1/4').advance_to(28)
        self.assertEqual(r.interval,ClosedInterval('3/20','1/5'))
        self.assertEqual(r.interval.midpoint(),F(7,40))

    def test_empty_stays_empty(self):
        def factory(cap,d,rng):
            if False: yield 0
            if cap==4: return ClosedInterval(0,'1/10')
            if cap==8: return ClosedInterval('1/5','1/4')
            return ClosedInterval(0,1)
        r=ConfidenceLadder(factory,zero_coin,delta='1/20',upper='1/4').advance_to(28)
        self.assertTrue(r.interval.empty)
        with self.assertRaises(ValueError): r.interval.midpoint()
        self.assertFalse(r.interval.contains('1/8'))

    def test_timeouts_preserve_interval(self):
        def factory(cap,d,rng):
            if cap==4:
                if False: yield 0
                return ClosedInterval('1/10','1/5')
            while True: yield 0
        r=ConfidenceLadder(factory,zero_coin,delta='1/20').advance_to(28)
        self.assertEqual(r.interval,ClosedInterval('1/10','1/5'))
        self.assertEqual(r.flips,24)

    def test_source_count_and_deltas(self):
        seen=[]
        def factory(cap,d,rng):
            seen.append((cap,d))
            for j in range(cap): yield j
            return ClosedInterval(0,1)
        r=ConfidenceLadder(factory,zero_coin,delta='1/20').advance_to(60)
        self.assertEqual(r.flips,60)
        self.assertEqual(seen,[(stage(j).flip_cap,F(1,20*(j+1)*(j+2))) for j in range(4)])

    def test_invalid_interval_program(self):
        def factory(cap,d,rng):
            if False: yield 0
            return (0,1)
        x=ConfidenceLadder(factory,zero_coin,delta='1/20')
        with self.assertRaises(TypeError): x.advance_to(4)
        with self.assertRaises(RuntimeError): x.advance_to(12)

    def test_budget_non_decreasing(self):
        x=ConfidenceLadder(full_interval,zero_coin,delta='1/20')
        a=x.advance_to(4)
        self.assertEqual(x.advance_to(4),a)
        with self.assertRaises(ValueError): x.advance_to(3)

    def test_exact_intervals(self):
        x=ClosedInterval('1/10','1/5')
        self.assertEqual(x.width,F(1,10))
        self.assertTrue(x.contains(F(1,8)))
        self.assertFalse(x.contains(0))
        with self.assertRaises(TypeError): ClosedInterval(.1,.2)

    def test_hoeffding_against_decimal(self):
        for n,h,d in [(1,0,F(1,20)),(100,10,F(1,100)),(10000,1000,F(1,1000000))]:
            x=bernoulli_interval(h,n,d)
            with localcontext() as ctx:
                ctx.prec=90
                r=((Decimal(2)/ (Decimal(d.numerator)/Decimal(d.denominator))).ln()/(2*n)).sqrt()
                m=Decimal(h)/n
                l=Decimal(x.lower.numerator)/Decimal(x.lower.denominator)
                u=Decimal(x.upper.numerator)/Decimal(x.upper.denominator)
                self.assertLessEqual(l,max(Decimal(0),m-r))
                self.assertGreaterEqual(u,min(Decimal(1),m+r))

    def test_log_bounds_decimal(self):
        for q in [F(1),F(3,2),F(2),F(17,3),F(10**100),F(101,100)]:
            a=_log_upper(q)
            with localcontext() as ctx:
                ctx.prec=100
                self.assertGreaterEqual(Decimal(a.numerator)/Decimal(a.denominator),
                                        (Decimal(q.numerator)/Decimal(q.denominator)).ln())

    def test_sqrt_upper_exact(self):
        for q in [F(0),F(1,2),F(2),F(4),F(17,13),F(10**100)]:
            a=_sqrt_upper(q)
            self.assertGreaterEqual(a*a,q)
            if a: self.assertLess((a-F(1,2**80))**2,q)

    def test_invalid_hoeffding_inputs(self):
        for args in [(0,0,F(1,20)),(4,3,F(1,20)),(True,3,F(1,20)),(0,3,0)]:
            with self.assertRaises((ValueError,TypeError)): bernoulli_interval(*args)

    def test_confidence_constructor(self):
        for d in [0,'.5',False,.05]:
            with self.assertRaises((TypeError,ValueError)):
                ConfidenceLadder(full_interval,zero_coin,delta=d)

if __name__ == '__main__':
    unittest.main()
