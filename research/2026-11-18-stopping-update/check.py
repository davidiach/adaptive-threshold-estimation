"""Exact Bayes optimization for the one-update stopping-time experiment at gap 1/5."""
from fractions import Fraction
from functools import cache
from itertools import product
from math import comb, isqrt

RADIX = 1450
SCALE = 10**24
HEADS = ((435, 609, 841, 1015), (435, 725, 925, 1015), (435, 525, 725, 1015))
TAILS = tuple(tuple(RADIX-x for x in row) for row in HEADS)
POINTS = (0, 3, 7, 10)
PRIOR = (2, 3, 3, 2)


def pilot_row(j, *, rounded):
    """Minimize over a fixed initial sequence and every prefix-dependent trigger."""
    start = tuple(p*h**j*(RADIX-h)**(18-j) for p, h in zip(PRIOR, HEADS[0]))
    choices = [tuple(a for a, cap in enumerate((7, j, 18-j)) if k < cap)
               for k in range(7)]

    @cache
    def children(w, a):
        return tuple(tuple(x*y for x, y in zip(w, row)) for row in (TAILS[a], HEADS[a]))

    @cache
    def fixed(ms, w):
        if ms:
            return sum(fixed(ms[1:], u) for u in children(w, ms[0]))
        total = sum(w)
        first = sum(x*y for x, y in zip(w, POINTS))
        second = sum(x*y*y for x, y in zip(w, POINTS))
        numerator = total*second - first**2
        denominator = 1000*RADIX**25*total
        return SCALE*numerator // denominator if rounded else Fraction(numerator, denominator)

    # Only committed actions commute. Retain the order of the initial plan.
    tails = [set(tuple(sorted(ms)) for ms in product(*choices[k:])) for k in range(8)]

    @cache
    def commit(k, w):
        return min(fixed(ms, w) for ms in tails[k])

    @cache
    def unused(ms, w):
        k = 6-len(ms)
        if not ms:
            return commit(k, w)
        stay = sum(unused(ms[1:], u) for u in children(w, ms[0]))
        return min(commit(k, w), stay)

    result = min(unused(ms, start) for ms in product(*choices[:6]))
    for fn in (unused, commit, fixed, children):
        fn.cache_clear()
    return result


if __name__ == "__main__":
    exact_rows = [pilot_row(j, rounded=False) for j in range(19)]
    rows = [pilot_row(j, rounded=True) for j in range(19)]
    assert exact_rows == exact_rows[::-1] and rows == rows[::-1]
    # Conditional on a particular pilot word, every strategy has 128 leaves.
    assert all(lo <= SCALE*q < lo + 128 for lo, q in zip(rows, exact_rows))
    lower = sum(comb(18, j)*v for j, v in enumerate(rows))
    exact = sum(comb(18, j)*v for j, v in enumerate(exact_rows))
    assert lower == 34910783257159239188322
    assert Fraction(186844275, 10**9)**2 <= Fraction(lower, SCALE) <= exact
    assert exact < Fraction(186844276, 10**9)**2
    assert exact > Fraction(186752, 10**6)**2
    print(f"Certified Bayes MSE lower bound: {lower}/{SCALE}")
    rms_floor = isqrt(exact.numerator*10**24 // exact.denominator)
    assert rms_floor == 186844275419
    print("Exact optimal Bayes RMS, rounded down to 12 places:", rms_floor, "/ 10^12")
