"""Exact Bayes lower bound for a suffix selected before its seven outcomes."""

from fractions import Fraction as Q
from itertools import product
from math import comb, prod


PRIOR = [(Q(0), Q(1, 5)), (Q(3, 10), Q(3, 10)),
         (Q(7, 10), Q(3, 10)), (Q(1), Q(1, 5))]
ADAPTIVE_MSE = Q(348763093753675683898541718818533, 10**34)


def binomial(n, p):
    return [comb(n, k) * p**k * (1 - p)**(n-k) for k in range(n+1)]


def action_risk(j, h, t):
    """Joint prior-weighted loss on pilot count j, minimized over estimates."""
    f = 7 - h - t
    rows = []
    for p, prior_mass in PRIOR:
        fresh = Q(3, 10) + Q(2, 5) * p
        # Conditional on a pilot head or tail, update the latent sign.
        head_again = (p * Q(7, 10)**2 + (1-p) * Q(3, 10)**2) / fresh
        head_after_tail = Q(21, 100) / (1 - fresh)
        pilot_mass = prior_mass * comb(18, j) * fresh**j * (1-fresh)**(18-j)
        groups = binomial(h, head_again), binomial(t, head_after_tail), binomial(f, fresh)
        rows.append([pilot_mass * prod(probs) for probs in product(*groups)])
        assert sum(rows[-1]) == pilot_mass

    risk = Q(0)
    for weights in zip(*rows):
        mean = sum(w*p for w, (p, _) in zip(weights, PRIOR)) / sum(weights)
        risk += sum(w*(p-mean)**2 for w, (p, _) in zip(weights, PRIOR))
    return risk


def main():
    risks = []
    schedules = 0
    for j in range(19):
        options = [(action_risk(j, h, t), h, t)
                   for h in range(min(7, j)+1)
                   for t in range(min(7-h, 18-j)+1)]
        # At position k a requested (k+1)st pilot head/tail must exist.
        reachable = {(0, 0)}
        for k in range(7):
            previous = reachable
            reachable = previous.copy()
            if k < j:
                reachable.update((h+1, t) for h, t in previous)
            if k < 18-j:
                reachable.update((h, t+1) for h, t in previous)
        assert reachable == {(h, t) for _, h, t in options}
        schedules += len(options)
        risk, h, t = min(options)
        risks.append(risk)
        print(f"j={j:2d}  head revisits={h}  tail revisits={t}  "
              f"row lower bound in units of 1e-10: {int(10**10*risk)}")
    assert risks == risks[::-1]
    assert schedules == 516
    total = sum(risks)
    lower = Q(18735887, 10**8)
    assert total > lower**2 > ADAPTIVE_MSE
    print(f"{schedules} count allocations. Bayes MSE lies between "
          f"{int(10**16*total)} and {int(10**16*total)+1} in units of 1e-16.")
    print(f"Certified precommitted RMS > {lower}; adaptive MSE = {ADAPTIVE_MSE}.")


if __name__ == "__main__":
    main()
