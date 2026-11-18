"""Four-point Bayes lower bound for one pilot-scheduled update at gap 1/5."""
from functools import cache
from itertools import product
from math import comb, prod

RADIX = 1450
PRECISION = 10**18
POINTS = (0, 3, 7, 10)  # ten times the sign probability
PRIOR = (2, 3, 3, 2)    # ten times the prior mass
# Heads following a pilot head, a pilot tail, or a fresh query, in radix units.
HEADS = ((435, 725, 925, 1015), (435, 525, 725, 1015), (435, 609, 841, 1015))


def allocations(j, start, length):
    for h in range(min(length, max(0, j-start)) + 1):
        for t in range(min(length-h, max(0, 18-j-start)) + 1):
            yield h, t, length-h-t


@cache
def likelihoods(sizes):
    return [tuple(prod(comb(n, k)*s[i]**k*(RADIX-s[i])**(n-k)
                       for n, k, s in zip(sizes, counts, HEADS)) for i in range(4))
            for counts in product(*(range(n+1) for n in sizes))]


def multiply(left, right):
    return tuple(x*y for x, y in zip(left, right))


def minimum_loss(weights):
    total = sum(weights)
    first = sum(w*x for w, x in zip(weights, POINTS))
    second = sum(w*x*x for w, x in zip(weights, POINTS))
    # Joint masses have denominator 10 * RADIX**25; squared loss in p
    # introduces another factor of 100. Floor each contribution down.
    return (PRECISION*(total*second-first**2)) // (1000*RADIX**25*total)


def pilot_row(j, split):
    pilot = tuple(w*comb(18, j)*s**j*(RADIX-s)**(18-j) for w, s in zip(PRIOR, HEADS[-1]))
    candidates = []
    for first in allocations(j, 0, split):
        loss = 0
        for observation in likelihoods(first):
            prefix = multiply(pilot, observation)
            loss += min(sum(minimum_loss(multiply(prefix, y)) for y in likelihoods(second))
                        for second in allocations(j, split, 7-split))
        candidates.append(loss)
    return min(candidates)


if __name__ == "__main__":
    rows = [[pilot_row(j, k) for k in range(8)] for j in range(19)]
    assert all(row[0] == row[7] for row in rows)
    assert rows == rows[::-1]
    mse = sum(min(row) for row in rows)
    assert mse == 34954180699172566
    assert mse * 10**18 > 186960371**2 * PRECISION
    print(f"MSE >= {mse}/{PRECISION}, RMS > 186960371/10^9")
