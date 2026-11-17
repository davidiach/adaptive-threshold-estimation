from fractions import Fraction as Q
from functools import cache
from itertools import product
from math import sqrt

import sympy as s


# Scalar identities used in the proof, including the one-flip Bayes update.
d, z, q = s.symbols("d z q", real=True)
increment = sum(
    (1 + 2*d*z*y)/2 * ((z + 2*d*y)/(1 + 2*d*z*y) - z)**2
    for y in (-1, 1)
)
assert s.factor(increment - 4*d**2*(1-z**2)**2/(1-4*d**2*z**2)) == 0
assert s.expand(1 - 4*d**2*z**2 - (1-z**2)**2 - z**2*((1-4*d**2)+(1-z**2))) == 0
assert s.expand(4*q*(1-q) + (1-2*q)**2) == 1
k, x = s.symbols("k x", positive=True)
t = k-1/k
assert s.factor(k*k*(1+x*x) - 1 - (x+t)**2 - (k*k-1)*(x-1/k)**2) == 0
assert t.subs(k, 2)**2 == Q(9, 4)
a = 1/(1+s.sqrt(3*x/2))
assert s.simplify(a**2*x/(2*(1-a)**2)) == s.Rational(1,3)
assert s.simplify(7*(4+x)/4 - (1+s.sqrt(3*x/2))**2 - (s.sqrt(x)/2-s.sqrt(6))**2) == 0


@cache
def policies(word, depth):
    if not depth:
        return [(word,)]
    left, right = (policies(word + (y,), depth-1) for y in (-1, 1))
    return [(word,)] + [l+r for l, r in product(left, right)]


def probabilities(d):
    def sign_word(word, sign):
        prob = Q(1)
        for y in word:
            prob *= Q(1,2) + y*sign*d
        return prob

    out = {}
    for n in range(5):
        for word in product((-1, 1), repeat=n):
            pp, pm = (sign_word(word, sign) for sign in (1, -1))
            mid = (pp+pm)/2
            mean = (pp-pm)/(2*mid) if mid else 0
            out[word] = (mid, mid*mean*mean)
    return out


count = 0
for gap in (Q(1,128), Q(1,8), Q(1,3), Q(1,2)):
    words = probabilities(gap)
    for leaves in policies((), 4):
        mass = sum(words[w][0] for w in leaves)
        work = sum(len(w)*words[w][0] for w in leaves)
        info = sum(words[w][1] for w in leaves)
        assert mass == 1 and info <= 4*gap**2 * work
        if set(leaves) == {(-1,), (1,)}:
            assert info == 4*gap**2 * work
        count += 1

print("Symbolic identities passed. Exact stopped-tree comparisons:", count)
c = (4*sqrt(21)-15)/25
print("RMS coefficient:", c, "improvement multiplier:", 64*c)
print("Certificate constants:", 3*sqrt(7)/2, 3*sqrt(7))
