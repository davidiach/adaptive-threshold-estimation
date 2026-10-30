"""Exact finite audits, NOT proofs of the inherited infinite-class lemmas.

Tests the new smoothing and adaptive KL bridge with selected component types,
creation, revisits, interleaving and data-dependent stopping. Every certified
inequality uses rational intervals, not floating-point tolerance.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt, prod
from pathlib import Path
import argparse
import hashlib
import json
import random


@dataclass(frozen=True)
class Bounds:
    lo: F
    hi: F

    def __add__(self, other):
        return Bounds(self.lo + other.lo, self.hi + other.hi)

    def scale(self, x):
        return Bounds(x*self.lo, x*self.hi) if x >= 0 else Bounds(x*self.hi, x*self.lo)

    def overlaps(self, other):
        return max(self.lo, other.lo) <= min(self.hi, other.hi)

    def record(self):
        return {"lower": str(self.lo), "upper": str(self.hi)}


@lru_cache(maxsize=8192)
def square_root(x, bits=100):
    assert isinstance(x, F) and x >= 0
    scale = 1 << bits
    k = isqrt((x.numerator << (2*bits)) // x.denominator)
    lo = F(k, scale)
    return Bounds(lo, lo if lo*lo == x else F(k+1, scale))


def unit_log(x, terms=30):
    assert 1 <= x <= 2
    z = (x-1)/(x+1)
    power = z
    value = F(0)
    for j in range(terms):
        value += 2*power/(2*j+1)
        power *= z*z
    return Bounds(value, value + 2*power/((2*terms+1)*(1-z*z)))


@lru_cache(maxsize=16384)
def natural_log(x):
    assert isinstance(x, F) and x > 0
    if x < 1:
        return natural_log(1/x).scale(F(-1))
    k = x.numerator.bit_length()-x.denominator.bit_length()
    if x < F(2)**k:
        k -= 1
    return unit_log(x/(F(2)**k)) + unit_log(F(2)).scale(k)


def kl(p, q):
    assert sum(p.values(), F(0)) == sum(q.values(), F(0)) == 1
    answer = Bounds(F(0), F(0))
    for key, value in p.items():
        if value:
            assert q.get(key, 0) > 0
            answer += natural_log(value/q[key]).scale(value)
    return Bounds(max(F(0), answer.lo), max(F(0), answer.hi))


def hellinger(p, q):
    assert sum(p.values(), F(0)) == sum(q.values(), F(0)) == 1
    if p == q:
        return Bounds(F(0), F(0))
    affinity = Bounds(F(0), F(0))
    for key in set(p) | set(q):
        affinity += square_root(p.get(key, F(0))*q.get(key, F(0)))
    return Bounds(max(F(0), 1-affinity.hi), max(F(0), 1-affinity.lo))


def mix(p, q, alpha=F(3, 4)):
    return {key: alpha*p.get(key, F(0))+(1-alpha)*q.get(key, F(0))
            for key in set(p) | set(q)}


def categorical_audit(count=200):
    rng = random.Random(20261030)
    pairs = [({0:F(1), 1:F(0)}, {0:F(0), 1:F(1)}),
             ({0:F(1,2), 1:F(1,2)}, {0:F(1,2), 1:F(1,2)})]
    for i in range(count):
        n = 2+i%5
        x = [rng.randrange(0,31) for _ in range(n)]
        y = [rng.randrange(0,31) for _ in range(n)]
        x[0] += 1
        y[-1] += 1
        pairs.append(({k:F(v,sum(x)) for k,v in enumerate(x)},
                      {k:F(v,sum(y)) for k,v in enumerate(y)}))
    minimum_slack = None
    for p,q in pairs:
        left, right = mix(p,q), mix(q,p)
        h = hellinger(p,q)
        for a,b in [(left,right), (right,left)]:
            divergence = kl(a,b)
            slack = F(8,3)*h.lo-divergence.hi
            assert slack >= 0
            if h.lo:
                minimum_slack = slack if minimum_slack is None else min(minimum_slack, slack)
    return {"categorical_pairs":len(pairs), "directed_inequalities":2*len(pairs),
            "minimum_nonzero_case_certified_slack":str(minimum_slack),
            "includes_singular_original_pair":True}


def coin_law(gaps, masses, signs):
    result = []
    for d,w,q in zip(gaps,masses,signs):
        assert 0 <= q <= F(1,2)
        result.extend([(w*(1-q), F(1,2)-d), (w*q,F(1,2)+d)])
    assert sum(w for w,p in result) == 1
    return tuple(result)


@lru_cache(maxsize=32768)
def word_mass(law, word):
    heads = sum(word)
    return sum(w*p**heads*(1-p)**(len(word)-heads) for w,p in law)


def make_policy(seed, cap):
    def policy(history):
        if len(history) >= cap:
            return None
        slots = 1+max((slot for slot,kind,bit in history), default=-1)
        code = seed + 17
        for slot,kind,bit in history:
            code = (code*131+7*slot+3*kind+bit) % 104729
        if len(history) >= 2 and code%13 == 0:
            return None
        if not slots or code%3 == 0:
            return slots, (code+sum(bit for _,_,bit in history))%2
        slot = code%slots
        kind = next(kind for i,kind,bit in history if i==slot)
        return slot,kind
    return policy


def experiment(policy, laws, *, special_slot=None, special_laws=None):
    leaves = {}
    def visit(history, words, types, mass):
        action = policy(history)
        if action is None:
            assert mass == prod(word_mass(
                special_laws[types[i]] if i==special_slot else laws[types[i]], word)
                for i,word in words.items())
            leaves[history] = mass
            return
        slot,kind = action
        assert slot in words or slot == len(words)
        assert slot not in types or kind == types[slot]
        law = special_laws[kind] if slot==special_slot else laws[kind]
        old = words.get(slot, ())
        denominator = word_mass(law,old)
        assert denominator > 0
        for bit in (0,1):
            numerator = word_mass(law,old+(bit,))
            if numerator:
                visit(history+((slot,kind,bit),), {**words,slot:old+(bit,)},
                      {**types,slot:kind}, mass*numerator/denominator)
    visit((),{}, {}, F(1))
    assert sum(leaves.values(),F(0)) == 1
    return leaves


def work(distribution, slot=None):
    return sum(p*(len(path) if slot is None else sum(i==slot for i,_,_ in path))
               for path,p in distribution.items())


def adaptive_audit(count=48):
    gaps = [(F(1,8),F(1,3)), (F(1,16),F(1,4))]
    masses = [(F(1,3),F(2,3)), (F(3,5),F(2,5))]
    q0 = [(F(0),F(1,8)), (F(1,8),F(1,16))]
    q1 = [(F(1,4),F(0)), (F(1,4),F(1,32))]
    lefts = [tuple(F(3,4)*a+F(1,4)*b for a,b in zip(x,y)) for x,y in zip(q0,q1)]
    rights = [tuple(F(1,4)*a+F(3,4)*b for a,b in zip(x,y)) for x,y in zip(q0,q1)]
    build = lambda qs: tuple(coin_law(d,w,q) for d,w,q in zip(gaps,masses,qs))
    original0, original1 = build(q0),build(q1)
    left, right = build(lefts),build(rights)
    null = build([(F(0),F(0)),(F(0),F(0))])
    counters = {"population_experiments":0,"hybrid_experiments":0,
                "exact_leaf_factorizations":0,"smoothing_checks":0,
                "null_work_domination_checks":0,"cost_partition_checks":0,
                "kl_sum_interval_checks":0}
    saw_revisit=saw_interleaving=saw_early_stop=saw_selected_types=False
    for seed in range(count):
        cap=3+seed%4
        policy=make_policy(seed,cap)
        p0,p1=experiment(policy,left),experiment(policy,right)
        assert set(p0)==set(p1)
        hybrids=[]
        divergence_sum=Bounds(F(0),F(0))
        charged=F(0)
        for i in range(cap):
            pi=experiment(policy,left,special_slot=i,special_laws=right)
            r=experiment(policy,left,special_slot=i,special_laws=original0)
            s=experiment(policy,left,special_slot=i,special_laws=original1)
            z=experiment(policy,left,special_slot=i,special_laws=null)
            assert mix(r,s)==p0
            assert mix(s,r)==pi
            h=hellinger(r,s)
            divergence=kl(p0,pi)
            assert divergence.hi<=F(8,3)*h.lo
            assert work(z,i)<=2*work(p0,i)
            charged+=work(p0,i)
            divergence_sum+=divergence
            hybrids.append(pi)
            counters["hybrid_experiments"]+=1
            counters["smoothing_checks"]+=1
            counters["null_work_domination_checks"]+=1
        assert charged==work(p0)
        counters["cost_partition_checks"]+=1
        for leaf,p in p0.items():
            assert p1[leaf]/p==prod(pi[leaf]/p for pi in hybrids)
            counters["exact_leaf_factorizations"]+=1
            labels=[i for i,_,_ in leaf]
            saw_revisit |= len(set(labels))<len(labels)
            saw_interleaving |= any(labels[k] in labels[:k-1] and labels[k]!=labels[k-1]
                                    for k in range(2,len(labels)))
            saw_early_stop |= len(leaf)<cap
        saw_selected_types |= any(len({kind for path in p0 for j,kind,bit in path if j==i})>1
                                  for i in range(1,cap))
        assert kl(p0,p1).overlaps(divergence_sum)
        counters["kl_sum_interval_checks"]+=1
        counters["population_experiments"]+=1
    assert saw_revisit and saw_interleaving and saw_early_stop and saw_selected_types
    counters["contains_revisits_interleaving_and_early_stopping"]=True
    counters["types_selected_from_observed_prehistory"]=True
    return counters


def algebra_audit():
    # 4(x^2+3y^2)-3(x+y)^2 = (x-3y)^2, coefficientwise.
    lhs={(2,0):F(4)-3,(1,1):F(-6),(0,2):F(12)-3}
    rhs={(2,0):F(1),(1,1):F(-6),(0,2):F(9)}
    assert lhs==rhs
    assert F(8,3)*2*42==224
    assert F(224,32**2)==F(7,32)<F(1,4)
    assert 840000**2>10*(8*33000)**2
    assert 210000**2>10*(2*33000)**2
    assert F(1,32)*F(1,2)*F(1,2)==F(1,128)
    assert F(1,16)**2 != F(1,4)*F(1,4)**2
    return {"whole_population_affineness_counterexample":True,"square_identity":True,"local_to_global_coefficient":"224",
            "kl_log_coefficient":"7/32","binary_testing_lower_coefficient":"1/4",
            "confidence_transfer_coefficient":"1/128",
            "hard_upper_rounded_constant":840000,"expected_upper_rounded_constant":210000}


def main():
    if not __debug__:
        raise RuntimeError("Run without -O: exact audit assertions must execute.")
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    result={"scope":"finite_exact_checks_not_a_universal_or_Lean_proof",
            "algebra":algebra_audit(),"categorical":categorical_audit(),
            "adaptive":adaptive_audit(),
            "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    text=json.dumps(result,indent=2)+"\n"
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text)
    print(text)


if __name__=="__main__":
    main()
