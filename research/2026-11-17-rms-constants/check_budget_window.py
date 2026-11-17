"""Arbitrary-precision certificate for the middle range of the sharp RMS theorem."""
from fractions import Fraction
from functools import cache


BINS = 2048
LAST_BARRIER = 20
SCALE = 1 << 32


def ceil_ratio(numerator, denominator):
    return -(-numerator // denominator)


@cache
def integral_upper(s):
    """Upper bound on integral (1-t^2)^2 H_s(t) for one rational bias s."""
    n = BINS
    # On [(j-1)/n,j/n], v=1-t^2 is at most weight[j-1]/n^2.
    weights = [n*n - left*left for left in range(n)]
    # Revealing the sign bounds v^2 H by v/s^2 on the entire interval.
    caps = [ceil_ratio(SCALE * weight * s.denominator**2,
                       n*n * s.numerator**2) for weight in weights]
    largest = [0] * n
    x = Fraction(0)
    for k in range(1, LAST_BARRIER + 1):
        x = (x + s) / (1 + s*x)
        slope = k/x - 1/s
        # For all barriers >= LAST_BARRIER, the length factor increases
        # with k. Replace the other occurrences of x_k by their upper bound 1.
        xmax = x if k < LAST_BARRIER else Fraction(1)
        p, q = xmax.as_integer_ratio()
        u, w = s.as_integer_ratio()
        c, d = slope.as_integer_ratio()
        # Clear all denominators in SCALE*v(left)^2*H(right).
        multiplier = SCALE * (1 + xmax/s) * q*w*d / n
        top, bottom = multiplier.as_integer_ratio()
        for j, weight in enumerate(weights, 1):
            denominator = bottom * (n*q - j*p) * (n*w + j*u) * (n*d*(k+1) - j*c)
            assert denominator >= 0
            if denominator:
                upper = ceil_ratio(top * weight**2, denominator)
            else:
                # The last bin of the infinite-barrier bound reaches t=1.
                assert j == n and k == LAST_BARRIER
                upper = caps[j-1]
            largest[j-1] = max(largest[j-1], upper)
    return Fraction(sum(map(min, largest, caps)), n*SCALE)


def cover_window():
    stack = [(Fraction(2, 5), Fraction(39, 40))]
    accepted = []
    while stack:
        lo, hi = stack.pop()
        # A bias-hi coin can simulate a bias-lo coin by independently
        # flipping outputs. Its unnormalized best information/work is larger.
        bound = (hi/lo)**2 * integral_upper(hi)
        if bound <= Fraction(2, 3):
            accepted.append(bound)
        else:
            if hi - lo < Fraction(1, 1 << 18):
                raise ValueError(f"Unresolved window {lo} to {hi}")
            mid = (lo + hi) / 2
            stack.extend([(lo, mid), (mid, hi)])
    return len(accepted), max(accepted)


if __name__ == "__main__":
    count, worst = cover_window()
    print(f"Certified {count} bias intervals, {BINS} bins in t, K={LAST_BARRIER}.")
    print(f"Largest integral upper bound {worst} <= 2/3.")
