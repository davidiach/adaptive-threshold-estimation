"""Exact two-gap estimator; no claim of rare-event efficiency.

The estimator receives a fresh-coin factory returning a zero-argument flip
callable. It never receives a sampled gap or sign. Fractions make the finite
checks exact; arithmetic cost is not included in the statistical flip budget.
"""

from fractions import Fraction as F


def specification(d1, d2, mass1):
    d1, d2, mass1 = map(F, (d1, d2, mass1))
    if not (0 < d1 < d2 <= F(1, 2) and 0 < mass1 < 1):
        raise ValueError("Need distinct positive gaps <= 1/2 and positive masses")
    x1, x2 = 2 * d1, 2 * d2
    den = 2 * x1 * x2 * (x1 + x2)
    a = (x1 * x1 + x1 * x2 + x2 * x2) / den
    b = -1 / den
    m2 = mass1 * x1 * x1 + (1 - mass1) * x2 * x2
    v = (1 - m2) * (m2 + F(1, 3))
    assert v > 0
    return dict(d1=d1, d2=d2, mass1=mass1, a=a, b=b, m2=m2, v=v)


def features(bits, spec):
    if len(bits) != 3 or any(bit not in (0, 1) for bit in bits):
        raise ValueError("Exactly three Bernoulli observations required")
    r1, r2, r3 = (2 * bit - 1 for bit in bits)
    A = F(r1 + r2 + r3, 3)
    B = r1 * r2 * r3
    C = F(r1 * r2 + r1 * r3 + r2 * r3, 3)
    return F(1, 2) + spec["a"] * A + spec["b"] * B, C - spec["m2"]


def estimate_with_pilot(coin_factory, spec, pilot_coins, production_coins, rho):
    """Return raw and clipped output with exact deterministic flip accounting.

    Independence of the coins supplied by coin_factory is a statistical
    assumption. The factory must draw one iid real coin per call, retaining
    its latent probability between its three flip calls.
    """
    if pilot_coins < 1 or production_coins < 1:
        raise ValueError("Both sample counts must be positive")
    rho = F(rho)
    if not 0 < rho <= F(1, 4):
        raise ValueError("Need 0 < rho <= 1/4")

    def fresh_features():
        coin = coin_factory()
        return features([coin(), coin(), coin()], spec)

    pilot = [fresh_features() for _ in range(pilot_coins)]
    beta = sum(y * z for y, z in pilot) / (pilot_coins * spec["v"])
    production = [fresh_features() for _ in range(production_coins)]
    raw = sum(y - beta * z for y, z in production) / production_coins
    return {
        "raw": raw,
        "clipped_to_rarity": min(rho, max(F(0), raw)),
        "coefficient": beta,
        "fresh_coins": pilot_coins + production_coins,
        "flips": 3 * (pilot_coins + production_coins),
    }
