"""New-module regressions; do not claim coverage of the existing toolkit."""
from copy import deepcopy
from decimal import Decimal, localcontext
from fractions import Fraction as F
from itertools import product
import json
import math
from pathlib import Path
import random
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from threshold_toolkit.rare_event_functional import (
    FiniteGapLaw, Interval, Precision, band_index, cost_entropy,
    evaluate_selection, exhaustive_certificate, log_interval, quantile_certificate,
    quantile_split, rational, sqrt_interval, suffix_search_size,
    transfer_enclosure, verify_certificate, round_up_within_bands, threshold_certificate,
)

P = Precision(bits=64, log_terms=24)

def bounds(c):
    return tuple(F(c['K_interval'][k]) for k in ('lower', 'upper'))

def brute(law, rho, budget):
    values = [evaluate_selection(law, bits, rho=rho, budget=budget, precision=P)
              for bits in product((0, 1), repeat=len(law.atoms))]
    return Interval(min(v.lower for v in values), min(v.upper for v in values))

def decimal(f):
    return Decimal(f.numerator) / Decimal(f.denominator)


class ExactArithmeticTests(unittest.TestCase):
    def test_rational_validation(self):
        self.assertEqual(rational('0.125'), F(1, 8))
        for value in [0.1, True, None, float('nan')]:
            with self.assertRaises(TypeError): rational(value)
        for value in ['NaN', '1/0', 'invalid']:
            with self.assertRaises(ValueError): rational(value)

    def test_sqrt_enclosures_by_exact_squaring(self):
        for x in [F(0), F(1), F(2), F(4, 9), F(1, 2**600), F(2**600), F(213, 177)]:
            v = sqrt_interval(x, 64)
            self.assertLessEqual(v.lower**2, x)
            self.assertGreaterEqual(v.upper**2, x)
            self.assertLessEqual(v.width, F(1, 2**64))
        self.assertEqual(sqrt_interval(F(4)).width, 0)

    def test_log_enclosures_independent_decimal(self):
        with localcontext() as c:
            c.prec = 110
            for x in [F(1), F(2), F(3, 2), F(7, 9), F(2**1000), F(1, 2**1000), F(123, 17)]:
                v = log_interval(x, 24)
                reference = decimal(x).ln()
                self.assertLessEqual(decimal(v.lower), reference)
                self.assertGreaterEqual(decimal(v.upper), reference)

    def test_scalar_8_over_5_polynomial_identity(self):
        # Exact algebra spot-check of the explicitly proved identity.
        for s,z in product([F(0),F(1,4),F(3,4),F(1)],[F(0),F(1,3),F(2)]):
            D=F(2,3)*s**3+2*s*s-F(58,15)*s+F(39,25)
            left=F(64,25)*z**4+F(181-260*s,50)*z*z+D
            p=2048*s**3-1968*s*s-584*s+861
            right=F(64,25)*(z*z+(181-260*s)/256)**2+p/3072
            self.assertEqual(left,right)
            self.assertGreaterEqual(p,F(12320,69))

    def test_precision_validation(self):
        for kwargs in [{'bits': True}, {'bits': 8}, {'log_terms': 0}, {'log_terms': 1.5}]:
            with self.assertRaises(ValueError): Precision(**kwargs)
        with self.assertRaises(ValueError): sqrt_interval(F(-1))
        with self.assertRaises(ValueError): log_interval(F(0))

    def test_entropy_zero_single_and_scaling(self):
        self.assertEqual(cost_entropy([F(0)], P), Interval(F(0), F(0)))
        self.assertEqual(cost_entropy([F(3)], P), Interval(F(3), F(3)))
        a = [F(2), F(7), F(0)]
        self.assertEqual(cost_entropy([3*x for x in a], P), cost_entropy(a, P).scale(F(3)))
        with self.assertRaises(ValueError): cost_entropy([F(-1)])

    def test_band_boundaries_exact(self):
        for j in range(50):
            upper, lower = F(1, 2**(j+1)), F(1, 2**(j+2))
            self.assertEqual(band_index(upper), j)
            self.assertEqual(band_index((upper+lower)/2), j)
            self.assertEqual(band_index(lower), j+1)
        self.assertEqual(band_index(F(1, 2**600)), 599)


class FunctionalTests(unittest.TestCase):
    def test_law_validation_and_duplicate_merge(self):
        law = FiniteGapLaw([('1/4', '1/3'), ('1/4', '2/3')])
        self.assertEqual(len(law.atoms), 1)
        for atoms in [[], [(0, 1)], [(1, 1)], [('1/4', '1/2')], [('1/4', -1)], [(True, 1)]]:
            with self.assertRaises((ValueError, TypeError)): FiniteGapLaw(atoms)

    def test_single_atom_closed_form(self):
        for d, rho, budget in product([F(1, 2), F(1, 4), F(1, 64)],
                                     [F(1, 4), F(1, 100)], [F(1), F(10**4), F(10**8)]):
            law = FiniteGapLaw([(d, 1)])
            expected_squared = min(rho*rho, rho / (budget*d*d))
            lo, hi = bounds(exhaustive_certificate(law, rho=rho, budget=budget, precision=P))
            self.assertLessEqual(lo*lo, expected_squared)
            self.assertGreaterEqual(hi*hi, expected_squared)

    def test_quantile_atom_is_split_exactly(self):
        law = FiniteGapLaw([('1/32', '1/20'), ('1/8', '3/20'), ('1/4', '4/5')])
        core, t = quantile_split(law, '1/10')
        self.assertEqual(core, (F(0), F(2,3), F(1)))
        self.assertEqual(t, F(1,8))
        self.assertEqual(sum(a.mass*(1-s) for a,s in zip(law.atoms,core)), F(1,10))

    def test_saturation_exact(self):
        law = FiniteGapLaw([('1/64', '1/10'), ('1/8', '9/10')])
        for budget in [F(1, 10), F(1), F(4096)]:
            q = quantile_certificate(law, rho='1/20', budget=budget, precision=P)
            self.assertEqual(bounds(q), (F(1,20),F(1,20)))

    def test_same_band_search_collapse(self):
        law = FiniteGapLaw([(F(101+i,400), F(1,60)) for i in range(60)])
        self.assertEqual(suffix_search_size(law), 61)
        c = exhaustive_certificate(law, rho='1/20', budget=10**6, precision=P)
        self.assertEqual(c['details']['states_evaluated'], 61)
        self.assertEqual(c['details']['original_subset_count'], str(2**60))
        self.assertLess(bounds(c)[1], F(1,20))

    def test_suffix_against_all_subsets_and_quantile_bound(self):
        rng = random.Random(20261030)
        # Eight candidates, with several distinct atoms sharing the same band.
        gaps = [F(3,8),F(5,16),F(7,32),F(3,16),F(5,32),F(7,64),F(3,32),F(5,64)]
        for trial in range(32):
            chosen = rng.sample(gaps, rng.randint(2, 7))
            raw = [rng.randrange(1, 21) for _ in chosen]
            total = sum(raw)
            law = FiniteGapLaw([(d,F(w,total)) for d,w in zip(chosen,raw)])
            rho = F(1,rng.choice([4,10,20,100]))
            budget = F(10**rng.randrange(2,9))
            direct = brute(law,rho,budget)
            lo,hi = bounds(exhaustive_certificate(law,rho=rho,budget=budget,precision=P))
            self.assertLessEqual(lo,direct.upper,(trial,law))
            self.assertGreaterEqual(hi,direct.lower,(trial,law))
            self.assertLessEqual(hi-lo,F(1,10**14))
            q = quantile_certificate(law,rho=rho,budget=budget,precision=P)
            qlo,qhi = bounds(q)
            self.assertLessEqual(qlo,direct.upper)
            self.assertGreaterEqual(qhi,direct.lower)

    def test_search_cap_fails_without_partial_certificate(self):
        law = FiniteGapLaw([(F(1,2**(i+2)),F(1,12)) for i in range(12)])
        with self.assertRaisesRegex(ValueError,'Complete suffix search'):
            exhaustive_certificate(law,rho='1/10',budget=10**8,max_states=100)

    def test_invalid_parameters(self):
        law=FiniteGapLaw([('1/4',1)])
        for rho,budget in [(0,10),('1/3',10),('1/10',0),('1/10',float('inf'))]:
            with self.assertRaises((TypeError,ValueError)):
                quantile_certificate(law,rho=rho,budget=budget)
        with self.assertRaises(ValueError):
            evaluate_selection(law,[2],rho='1/10',budget=10)

    def test_very_small_positive_gap_no_underflow(self):
        law = FiniteGapLaw([(F(1,2**600),1)])
        c = exhaustive_certificate(law,rho='1/100',budget=2**1300,precision=P)
        lo,hi=bounds(c)
        self.assertGreater(hi,0)
        target_squared=F(1,100*2**100)
        self.assertLessEqual(lo*lo,target_squared)
        self.assertGreaterEqual(hi*hi,target_squared)

    def test_budget_monotonicity(self):
        law=FiniteGapLaw([('1/64','1/10'),('1/4','9/10')])
        for b in [100,10000,10**6]:
            lo,hi=bounds(exhaustive_certificate(law,rho='1/10',budget=b,precision=P))
            lo4,hi4=bounds(exhaustive_certificate(law,rho='1/10',budget=4*b,precision=P))
            self.assertLessEqual(lo4,hi)
            self.assertGreaterEqual(hi4,lo/2)

    def test_total_variation_stability_examples(self):
        for eta in [F(1,100),F(1,10)]:
            first=FiniteGapLaw([('1/64','1/4'),('1/4','3/4')])
            second=FiniteGapLaw([('1/64',F(1,4)+eta),('1/4',F(3,4)-eta)])
            for b in [10**4,10**6]:
                l1,u1=bounds(exhaustive_certificate(first,rho='1/10',budget=b,precision=P))
                l2,u2=bounds(exhaustive_certificate(second,rho='1/10',budget=b,precision=P))
                self.assertLessEqual(l2,u1+eta)
                self.assertLessEqual(l1,u2+eta)

    def test_band_preserving_rounding_examples(self):
        first=FiniteGapLaw([('3/32','1/10'),('3/16','2/5'),('3/8','1/2')])
        second=FiniteGapLaw([('1/8','1/10'),('1/4','2/5'),('1/2','1/2')])
        for b in [10**4,10**6]:
            l1,u1=bounds(exhaustive_certificate(first,rho='1/10',budget=b,precision=P))
            l2,u2=bounds(exhaustive_certificate(second,rho='1/10',budget=b,precision=P))
            self.assertLessEqual(l2,u1)
            self.assertLessEqual(l1,F(4,3)*u2)

    def test_rounding_helper_enforces_premises(self):
        law=FiniteGapLaw([(F(101+i,400),F(1,60)) for i in range(60)])
        rounded=round_up_within_bands(law,subdivisions=4)
        self.assertLessEqual(rounded.factor,F(5,4))
        self.assertLessEqual(len(rounded.law.atoms),4)
        for a,d in zip(law.atoms,rounded.destinations):
            self.assertEqual(band_index(a.gap),band_index(d))
            self.assertLessEqual(a.gap,d)
            self.assertLessEqual(d,rounded.factor*a.gap)
        lo,hi=bounds(exhaustive_certificate(law,rho='1/10',budget=10**6,precision=P))
        l2,u2=bounds(exhaustive_certificate(rounded.law,rho='1/10',budget=10**6,precision=P))
        self.assertLessEqual(l2,hi)
        self.assertLessEqual(lo,rounded.factor*u2)

    def test_global_threshold_is_upper_not_exact(self):
        law=FiniteGapLaw([('1/4','9999/10000'),('1/2','1/10000')])
        exact=exhaustive_certificate(law,rho='1/4',budget=10**8,precision=P)
        scan=threshold_certificate(law,rho='1/4',budget=10**8,precision=P)
        self.assertEqual(exact['details']['best_hard_witness'],['1','0'])
        self.assertGreater(bounds(scan)[1],bounds(exact)[1])
        self.assertFalse(scan['details']['globally_exact'])
        self.assertEqual(scan['details']['states_evaluated'],3)

    def test_threshold_scan_improves_point_atom_quantile(self):
        law=FiniteGapLaw([('1/4',1)])
        q=quantile_certificate(law,rho='1/4',budget=10**8,precision=P)
        v=threshold_certificate(law,rho='1/4',budget=10**8,precision=P)
        e=exhaustive_certificate(law,rho='1/4',budget=10**8,precision=P)
        self.assertEqual(bounds(v)[1],bounds(e)[1])
        self.assertLess(bounds(v)[1],F(q['details']['Q_interval']['upper']))

    def test_cross_band_rounding_is_not_safe(self):
        original=FiniteGapLaw([('249/1000','1/2'),('251/1000','1/2')])
        merged=FiniteGapLaw([('251/1000',1)])
        lo,hi=bounds(exhaustive_certificate(original,rho='1/100',budget=10**8,precision=P))
        l2,u2=bounds(exhaustive_certificate(merged,rho='1/100',budget=10**8,precision=P))
        self.assertGreater(lo,F(251,249)*u2)

    def test_transfer_enclosure(self):
        result=transfer_enclosure(Interval(F(1,100),F(2,100)),rounding_factor='11/10',tv_radius='1/1000',rho='1/10')
        self.assertEqual(result,Interval(F(9,1000),F(23,1000)))


class CertificateIntegrityTests(unittest.TestCase):
    def setUp(self):
        self.law=FiniteGapLaw([('1/32','1/10'),('1/4','9/10')])
        self.kw={'rho':'1/20','budget':10**6,'precision':P}

    def test_roundtrip_both_methods(self):
        for fn in [quantile_certificate,threshold_certificate,exhaustive_certificate]:
            c=json.loads(json.dumps(fn(self.law,**self.kw)))
            self.assertTrue(verify_certificate(c,self.law,rho='1/20',budget=10**6))

    def test_rejects_wrong_external_instance(self):
        c=quantile_certificate(self.law,**self.kw)
        self.assertFalse(verify_certificate(c,self.law,rho='1/10',budget=10**6))
        self.assertFalse(verify_certificate(c,self.law,rho='1/20',budget=10**7))
        other=FiniteGapLaw([('1/32','1/5'),('1/4','4/5')])
        self.assertFalse(verify_certificate(c,other,rho='1/20',budget=10**6))

    def test_rejects_tampering(self):
        c=exhaustive_certificate(self.law,**self.kw)
        mutations=[
            lambda x:x.update(scope='statistical_risk'),
            lambda x:x.update(schema='other'),
            lambda x:x.update(base_commit='fake'),
            lambda x:x.update(method='not-a-method'),
            lambda x:x.update(instance_sha256='0'*64),
            lambda x:x['K_interval'].update(upper='0'),
            lambda x:x['K_interval'].update(lower='1/20'),
            lambda x:x['details'].update(states_evaluated=1),
            lambda x:x['details'].update(all_states_evaluated=False),
            lambda x:x['precision'].update(bits=True),
            lambda x:x['instance'].update(budget='1'),
            lambda x:x.update(extra_ignored_field=True),
        ]
        for mutate in mutations:
            bad=deepcopy(c); mutate(bad)
            self.assertFalse(verify_certificate(bad,self.law,rho='1/20',budget=10**6),bad)

    def test_rejects_missing_and_malformed_fields(self):
        c=quantile_certificate(self.law,**self.kw)
        for key in list(c):
            bad=deepcopy(c);del bad[key]
            self.assertFalse(verify_certificate(bad,self.law,rho='1/20',budget=10**6))
        for bad in [None,[],{},True]:
            self.assertFalse(verify_certificate(bad,self.law,rho='1/20',budget=10**6))

    def test_recheck_cap(self):
        c=exhaustive_certificate(self.law,**self.kw)
        self.assertFalse(verify_certificate(c,self.law,rho='1/20',budget=10**6,max_recheck_states=1))

if __name__=='__main__':unittest.main()
