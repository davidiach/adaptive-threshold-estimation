"""Exact polynomial proof of the three-flip Fisher bound and its depth-four obstruction."""
from collections import Counter
from fractions import Fraction
from itertools import product

import sympy as sp


X, Y = sp.symbols("X Y")


def poly(expr):
    return sp.Poly(expr, X, Y, domain=sp.ZZ)


def trees(word, remaining):
    if remaining == 0:
        return [(word,)]
    left = trees(word + "+", remaining - 1)
    right = trees(word + "-", remaining - 1)
    return [(word,)] + [a + b for a, b in product(left, right)]


def cleared_surplus(leaves):
    """Positive denominator times a²W - (1-m²)I in the odds coordinates."""
    one, x, y = poly(1), poly(X), poly(Y)
    depth = max(map(len, leaves))
    work = poly(0)
    information = []
    # Multiply the surplus by (2+Y)*(2+X)^(depth+2). The work term
    # becomes a polynomial and each information term retains only mass
    # in its denominator. Each mass is positive throughout the quadrant.
    for (n, k), count in Counter((len(s), s.count("+")) for s in leaves).items():
        pos, neg = (one+x)**k, (one+x)**(n-k)
        mass = (one+y)*pos + neg
        work += count*n*mass*(2+x)**(depth-n)*x**2
        if pos != neg:
            term = count*(one+y)*(pos-neg)**2*(2+x)**(depth+2-n)
            information.append((term,mass))
    numerator, denominator = work, one
    for term, divisor in information:
        numerator = numerator*divisor - term*denominator
        denominator *= divisor
    return numerator


def nonnegative_on_quadrant(p, splits_left=2):
    if all(c >= 0 for c in p.coeffs()):
        return 1
    if splits_left == 0:
        raise ValueError("Polynomial positivity unresolved")
    # X>=Y: (X,Y)=(s+t,t). Y>=X: (X,Y)=(t,s+t).
    swapped = sp.Poly.from_dict({(j,i): c for (i,j),c in p.terms()}, (X,Y))
    substitution = poly(X+Y)
    return (nonnegative_on_quadrant(p.compose(substitution), splits_left-1)
            + nonnegative_on_quadrant(swapped.compose(substitution), splits_left-1))


def four_flip_obstruction():
    a, m = Fraction(6,7), Fraction(19,20)
    work = info = total = Fraction(0)
    for word in ("+", "-+", "---", "--++", "--+-"):
        n, k = len(word), word.count("+")
        pos = ((1+a)/2)**k*((1-a)/2)**(n-k)
        neg = ((1-a)/2)**k*((1+a)/2)**(n-k)
        mass = ((1+m)*pos+(1-m)*neg)/2
        total += mass
        work += n*mass
        info += (pos-neg)**2/(4*mass)
    assert total == 1
    excess = (1-m*m)*info-a*a*work
    assert excess == Fraction(11469627,2937056864) > 0
    return excess


if __name__ == "__main__":
    policies = trees("",3)[1:]
    assert len(policies) == 25
    cones = sum(nonnegative_on_quadrant(cleared_surplus(tree)) for tree in policies)
    print(f"Certified all {len(policies)} root-active trees on {cones} polynomial cones.")
    print(f"Depth-four excess (1-m^2)I-a^2 W = {four_flip_obstruction()}.")
