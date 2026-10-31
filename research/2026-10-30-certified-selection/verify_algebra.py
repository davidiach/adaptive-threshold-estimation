"""Exact coefficient checks for the scalar 8/5 comparison lemma.

This verifies polynomial identities, not the surrounding entropy theorem.
All arithmetic is rational. No CAS or floating-point dependencies. Apache-2.0.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from runtime_output import compare, output_directory

# Sparse bivariate polynomials in (s,z).
def add(*polys):
    out = {}
    for p in polys:
        for key, value in p.items():
            out[key] = out.get(key, F(0)) + value
    return {key: value for key, value in out.items() if value}

def scale(p, c):
    return {key: value * F(c) for key, value in p.items() if value * F(c)}

def mul(p, q):
    out = {}
    for (a,b), x in p.items():
        for (c,d), y in q.items():
            key = (a+c,b+d)
            out[key] = out.get(key, F(0)) + x*y
    return {key: value for key, value in out.items() if value}

def power(p,n):
    answer = {(0,0):F(1)}
    for _ in range(n):
        answer = mul(answer,p)
    return answer

def main():
    out_dir, writing = output_directory(__doc__)
    one = {(0,0):F(1)}
    s = {(1,0):F(1)}
    z2 = {(0,2):F(1)}
    # Polynomial left after applying 2ab <= (3/2)a^2 + (2/3)b^2.
    left = {(0,4): F(64,25), (0,2): F(181,50), (1,2): -F(26,5),
            (3,0): F(2,3), (2,0): F(2), (1,0): -F(58,15),
            (0,0): F(39,25)}
    p = {(3,0):F(2048),(2,0):F(-1968),(1,0):F(-584),(0,0):F(861)}
    square = power(add(z2,scale(one,F(181,256)),scale(s,-F(260,256))),2)
    right = add(scale(square,F(64,25)),scale(p,F(1,3072)))
    assert left == right, 'Completion-of-square identity failed'
    w = add(s,scale(one,-F(3,4)))
    shifted = add(scale(power(w,3),2048),scale(power(w,2),2640),scale(w,-80),scale(one,180))
    assert shifted == p, 'Shifted cubic identity failed'
    lower = add(scale(power(w,2),1104),scale(w,-80),scale(one,180))
    square_lower = add(scale(power(add(w,scale(one,-F(5,138))),2),1104),scale(one,F(12320,69)))
    assert lower == square_lower, 'Positive quadratic identity failed'
    difference = add(p,scale(lower,-1))
    nonnegative = scale(mul(power(w,2),add(w,scale(one,F(3,4)))),2048)
    assert difference == nonnegative, 'Nonnegative remainder identity failed'
    assert F(12320,69) > 0
    record = {
        'scope': 'exact rational polynomial identities; not full theorem formalization',
        'checks_passed': 4,
        'coefficient_method': 'sparse bivariate polynomials with Fraction arithmetic',
        'identities': [
            'Young lower polynomial = (64/25)(z^2+(181-260s)/256)^2 + p(s)/3072',
            'p(s) = 2048w^3+2640w^2-80w+180, w=s-3/4',
            '1104w^2-80w+180 = 1104(w-5/138)^2+12320/69',
            'p(s)-(1104w^2-80w+180) = 2048w^2(w+3/4)'
        ],
        'remaining_human_readable_inference': 'For s in [0,1], w+3/4=s>=0, so every remainder is nonnegative and 12320/69>0.'
    }
    (out_dir/'algebra.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))
    return 0 if writing else compare(out_dir, ['algebra.json'])

if __name__=='__main__':
    sys.exit(main())
