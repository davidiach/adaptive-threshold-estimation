"""Floating-point checks of the statements in paper/v6/psi-window.tex.

This is numerical evidence, not a proof and not a formal verification. Every
inequality tested here has a paper proof in that file; the script guards the
constants and the case analysis against slips. It uses only the standard
library and a fixed seed, and exits nonzero if any inequality fails.

Part A draws random finite gap laws and checks, for the variational modulus
Psi, the entropy-free and entropy-weighted quantile forms Q0 and Q, and the
selection functionals K0 and K (by enumerating hard selections):

    Q0/sqrt(2) <= Psi <= K0 <= min(K, Q0),   K <= Q <= sqrt(1+Ent) * Q0,

the sharpness example for the factor sqrt(2), and the core-dominated converse.
Psi is evaluated at the feasible allocation min(1, c^2/d^2) with full budget
and compared with a random search over feasible allocations.

Part B evaluates the quantile core of the power law F(d) = (d/a)^alpha exactly
band by band and checks the cost identity, the entropy bounds

    (1/2) Phi (1+log N) <= a^2 Gamma_kappa <= 3.83 Phi (1+log N),

the resulting bounds on Q, the window bounds for 3/2 <= alpha <= 3, and the
fixed-exponent form of the remark that follows the window corollary.
"""
from __future__ import annotations

import math
import random
import sys

TOL = 1e-9
FAILURES: list[str] = []


def require(condition: bool, message: str) -> None:
    if not condition:
        FAILURES.append(message)


# --------------------------------------------------------------------------
# Shared definitions (paper/v6: canonical bands, G, the quantile split)
# --------------------------------------------------------------------------

def band(d: float) -> int:
    """Index j of the canonical band (2^-(j+2), 2^-(j+1)] containing d."""
    j = math.floor(-math.log2(d)) - 1
    while d <= 2.0 ** -(j + 2):
        j += 1
    while d > 2.0 ** -(j + 1):
        j -= 1
    return j


def cost_entropy(costs: list[float]) -> float:
    """G(a) = A + sum a_j log(A/a_j)."""
    total = sum(costs)
    if total <= 0:
        return 0.0
    return total + sum(c * math.log(total / c) for c in costs if c > 0)


def gamma(atoms: list[tuple[float, float]]) -> float:
    by_band: dict[int, float] = {}
    for d, mass in atoms:
        if mass > 0:
            by_band[band(d)] = by_band.get(band(d), 0.0) + mass / d ** 2
    return cost_entropy(list(by_band.values()))


def quantile_split(law, rho):
    """nu: the mass rho of smallest gaps (a boundary atom is split); kappa: the rest."""
    nu, kappa, left = [], [], rho
    for d, w in law:
        take = min(w, max(left, 0.0))
        left -= take
        nu.append((d, take))
        kappa.append((d, w - take))
    return nu, kappa


def psi_value(law, rho, h):
    """The allocation v = min(1, c^2/d^2) with int v dmu = rho; it is feasible."""
    budget = lambda c: sum(w * min(1.0, c * c / (d * d)) for d, w in law)
    lo, hi = 0.0, 0.5
    for _ in range(200):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if budget(mid) < rho else (lo, mid)
    c = (lo + hi) / 2
    total = 0.0
    for d, w in law:
        v = min(1.0, c * c / (d * d))
        total += w * min(v, h * math.sqrt(v) / d)
    return total


def psi_random_search(law, rho, h, trials, rng):
    best = 0.0
    for _ in range(trials):
        v = [rng.random() ** rng.choice([0.3, 1, 3]) for _ in law]
        used = sum(w * x for (_, w), x in zip(law, v))
        if used > rho:
            v = [x * rho / used for x in v]
        best = max(best, sum(w * min(x, h * math.sqrt(x) / d) for (d, w), x in zip(law, v)))
    return best


def selection_values(law, rho, h):
    """K0 (inverse-square cost) and K (cost entropy), over hard selections.

    Both objectives are concave in the selected submeasure plus a linear
    term, so hard selections attain the infimum for a finite law.
    """
    k0 = k = rho
    n = len(law)
    for mask in range(1 << n):
        chosen = [law[i] for i in range(n) if mask >> i & 1]
        rest = sum(w * min(1.0, h / d) for i, (d, w) in enumerate(law) if not mask >> i & 1)
        k0 = min(k0, rest + h * math.sqrt(rho * sum(w / d ** 2 for d, w in chosen)))
        k = min(k, rest + h * math.sqrt(rho * gamma(chosen)))
    return k0, k


def part_a(rng: random.Random, trials: int = 4000) -> dict[str, float]:
    extremes = {"min Psi/Q0": 9.0, "max Psi/Q0": 0.0, "min K0/Psi": 9.0, "max K0/Q0": 0.0,
                "min K/K0": 9.0, "max Q/K": 0.0, "max Q/(sqrt(1+Ent) Q0)": 0.0,
                "max search/Psi": 0.0, "min Q/(sqrt(1+Ent) Q0), core-dominated": 9.0}
    for trial in range(trials):
        n = rng.randint(1, 9)
        kind = rng.choice(["log", "dyadic", "linear"])
        if kind == "log":
            gaps = {0.5 * 10 ** (-rng.uniform(0, 6)) for _ in range(n)}
        elif kind == "dyadic":
            gaps = {2.0 ** -rng.randint(1, 30) for _ in range(n)}
        else:
            gaps = {0.5 * rng.uniform(0.001, 1) for _ in range(n)}
        gaps = sorted(gaps)
        weights = [rng.random() ** rng.choice([1, 4]) + 1e-9 for _ in gaps]
        total = sum(weights)
        law = [(d, w / total) for d, w in zip(gaps, weights)]
        rho = rng.choice([0.25, 0.1, 0.01, 1e-3, 1e-5]) * rng.uniform(0.3, 1)
        h = 10 ** (-rng.uniform(0, 7))

        nu, kappa = quantile_split(law, rho)
        tail = sum(m * min(1.0, h / d) for d, m in nu)
        cost = sum(m / d ** 2 for d, m in kappa)
        gam = gamma(kappa)
        entropy = gam / cost - 1
        q0 = min(rho, tail + h * math.sqrt(rho * cost))
        q = min(rho, tail + h * math.sqrt(rho * gam))
        psi = psi_value(law, rho, h)
        k0, k = selection_values(law, rho, h)

        where = f"trial {trial}: law={law} rho={rho} h={h}"
        require(psi >= q0 / math.sqrt(2) * (1 - TOL), "Q0/sqrt2 <= Psi fails, " + where)
        require(psi <= k0 * (1 + TOL), "Psi <= K0 fails, " + where)
        require(k0 <= min(k, q0) * (1 + TOL), "K0 <= min(K, Q0) fails, " + where)
        require(k <= q * (1 + TOL), "K <= Q fails, " + where)
        require(q <= math.sqrt(1 + entropy) * q0 * (1 + TOL), "Q <= sqrt(1+Ent) Q0 fails, " + where)
        core = h * math.sqrt(rho * cost)
        if tail <= core and tail + h * math.sqrt(rho * gam) <= rho:
            ratio = q / (math.sqrt(1 + entropy) * q0)
            require(ratio >= 0.5 * (1 - TOL), "core-dominated converse fails, " + where)
            extremes["min Q/(sqrt(1+Ent) Q0), core-dominated"] = min(
                extremes["min Q/(sqrt(1+Ent) Q0), core-dominated"], ratio)
        if trial % 8 == 0:
            found = psi_random_search(law, rho, h, 400, rng)
            require(found <= psi * (1 + 1e-7), "random search beats the allocation, " + where)
            extremes["max search/Psi"] = max(extremes["max search/Psi"], found / psi)
        extremes["min Psi/Q0"] = min(extremes["min Psi/Q0"], psi / q0)
        extremes["max Psi/Q0"] = max(extremes["max Psi/Q0"], psi / q0)
        extremes["min K0/Psi"] = min(extremes["min K0/Psi"], k0 / psi)
        extremes["max K0/Q0"] = max(extremes["max K0/Q0"], k0 / q0)
        extremes["min K/K0"] = min(extremes["min K/K0"], k / k0)
        extremes["max Q/K"] = max(extremes["max Q/K"], q / k)
        extremes["max Q/(sqrt(1+Ent) Q0)"] = max(extremes["max Q/(sqrt(1+Ent) Q0)"],
                                                 q / (math.sqrt(1 + entropy) * q0))

    # Sharpness of sqrt(2): rho at gap d1 and 1-rho at d2 = d1 sqrt((1-rho)/rho), h <= d1/2.
    for rho, d1 in ((0.2, 0.125), (0.1, 0.05), (0.25, 0.25), (0.01, 0.01)):
        d2 = d1 * math.sqrt((1 - rho) / rho)
        law = [(d1, rho), (d2, 1 - rho)]
        for h in (d1 / 2, d1 / 10, d1 / 1000):
            q0 = min(rho, h * rho / d1 + h * math.sqrt(rho * (1 - rho) / d2 ** 2))
            psi = psi_value(law, rho, h)
            require(abs(psi * math.sqrt(2) / q0 - 1) < 1e-9, f"sharpness example rho={rho} d1={d1} h={h}")
            require(abs(psi - math.sqrt(2) * h * rho / d1) < 1e-12, "sharpness value")
    return extremes


# --------------------------------------------------------------------------
# Part B: power laws
# --------------------------------------------------------------------------

def phi(alpha: float, log_inv_rho: float) -> float:
    """Phi = alpha * int_{rho^(1/alpha)}^1 s^(alpha-3) ds."""
    e = alpha - 2
    u = e * log_inv_rho / alpha
    if abs(u) < 1e-9:
        return log_inv_rho * (1 - u / 2)
    return alpha * (-math.expm1(-u)) / e


def scales(alpha: float, log_inv_rho: float) -> float:
    """N = min(1 + log2(1/rho)/alpha, max(1, 1/|alpha-2|))."""
    m = log_inv_rho / (alpha * math.log(2))
    return 1 + m if alpha == 2 else min(1 + m, max(1.0, 1 / abs(alpha - 2)))


def core_band_costs(alpha: float, a: float, log_inv_rho: float) -> list[float]:
    """a^2 times the inverse-square cost of the core (a rho^(1/alpha), a] in each canonical band."""
    e = alpha - 2
    log_s_t = -log_inv_rho / alpha
    costs = []
    j = math.floor(-math.log2(a)) - 2
    while True:
        lo = -(j + 2) * math.log(2) - math.log(a)      # band edges in log(s), s = d/a
        hi = -(j + 1) * math.log(2) - math.log(a)
        lo2, hi2 = max(lo, log_s_t), min(hi, 0.0)
        if hi2 > lo2:
            if abs(e) < 1e-12:
                costs.append(alpha * (hi2 - lo2))
            else:
                costs.append(alpha * math.exp(e * lo2) * math.expm1(e * (hi2 - lo2)) / e)
        if lo <= log_s_t:
            break
        j += 1
    return costs


def tail_term(alpha: float, x: float, log_inv_rho: float) -> float:
    """T = x^alpha + alpha x int_x^{rho^(1/alpha)} s^(alpha-2) ds, for x < rho^(1/alpha)."""
    s = math.exp(-log_inv_rho / alpha)
    if abs(alpha - 1) < 1e-12:
        return x + x * math.log(s / x)
    return x ** alpha + alpha * x * (s ** (alpha - 1) - x ** (alpha - 1)) / (alpha - 1)


def part_b(rng: random.Random) -> dict[str, float]:
    extremes = {"min a^2 Gamma/[Phi(1+log N)]": 9.0, "max a^2 Gamma/[Phi(1+log N)]": 0.0,
                "min Q/R_formula": 9.0, "max Q/R_formula": 0.0,
                "max T/(x sqrt(rho Phi)), window": 0.0,
                "min R_formula/min(rho,Y), window": 9.0, "max R_formula/min(rho,Y), window": 0.0,
                "min Y/[x rho^e sqrt((1+log(1/eps))/eps)], u>=1": 9.0,
                "max Y/[x rho^e sqrt((1+log(1/eps))/eps)], u>=1": 0.0}
    alphas = [0.05, 0.1, 0.3, 0.5, 0.8, 1, 1.2, 1.5, 1.7, 1.9, 1.95, 1.99, 1.999, 1.9999, 2,
              2.0001, 2.001, 2.01, 2.05, 2.1, 2.3, 2.5, 2.8, 3, 3.5, 4]
    alphas += [rng.uniform(0.02, 4) for _ in range(60)] + [2 + rng.choice([-1, 1]) * 10 ** -rng.uniform(0, 6)
                                                            for _ in range(60)]
    logs = [math.log(4), 1.5, 2, 3, 5, 8, 12, 20, 40, 80, 150, 300, 600]
    for alpha in alphas:
        for log_inv_rho in logs + [rng.uniform(math.log(4), 500) for _ in range(6)]:
            if (2 - alpha) * log_inv_rho / alpha > 600:      # rho^(1-2/alpha) overflows a float
                continue
            for a in [0.5, 0.4, 0.3, 0.25, 0.13, 0.07, 0.01, 1e-4] + [rng.uniform(1e-5, 0.5) for _ in range(4)]:
                costs = core_band_costs(alpha, a, log_inv_rho)
                total = sum(costs)
                p = phi(alpha, log_inv_rho)
                where = f"alpha={alpha} log(1/rho)={log_inv_rho} a={a}"
                require(abs(total / p - 1) < 1e-6, "cost identity fails, " + where)
                n = scales(alpha, log_inv_rho)
                gam = cost_entropy(costs)
                ratio = gam / (p * (1 + math.log(n)))
                require(0.5 * (1 - TOL) <= ratio <= 3.83 * (1 + TOL), f"entropy bounds fail ({ratio}), " + where)
                extremes["min a^2 Gamma/[Phi(1+log N)]"] = min(extremes["min a^2 Gamma/[Phi(1+log N)]"], ratio)
                extremes["max a^2 Gamma/[Phi(1+log N)]"] = max(extremes["max a^2 Gamma/[Phi(1+log N)]"], ratio)
                eps = abs(alpha - 2)
                u = eps * log_inv_rho / alpha
                if 1.5 <= alpha <= 3 and eps > 0 and u >= 1:
                    # Remark: Y = x rho^min(1/2, 1-1/alpha) sqrt((1+log(1/eps))/eps), up to constants.
                    log_phi = math.log(alpha / eps) + math.log(-math.expm1(-u)) + (u if alpha < 2 else 0.0)
                    exponent = min(0.5, 1 - 1 / alpha)
                    log_ratio = (0.5 * (-log_inv_rho + log_phi + math.log(1 + math.log(n)))
                                 + exponent * log_inv_rho
                                 - 0.5 * math.log((1 + math.log(1 / eps)) / eps))
                    require(abs(n - 1 / eps) < 1e-9 * n, "N differs from 1/eps, " + where)
                    require(math.log(0.97) <= log_ratio <= math.log(1.74), f"remark fails ({log_ratio}), " + where)
                    name = "Y/[x rho^e sqrt((1+log(1/eps))/eps)], u>=1"
                    extremes["min " + name] = min(extremes["min " + name], math.exp(log_ratio))
                    extremes["max " + name] = max(extremes["max " + name], math.exp(log_ratio))
                if log_inv_rho > 200:                        # rho underflows relative to the other terms
                    continue
                rho = math.exp(-log_inv_rho)
                s = math.exp(-log_inv_rho / alpha)
                for x in [s * 10 ** -rng.uniform(0, 8) for _ in range(4)]:
                    t = tail_term(alpha, x, log_inv_rho)
                    y = x * math.sqrt(rho * p * (1 + math.log(n)))
                    q = min(rho, t + x * math.sqrt(rho * gam))
                    formula = min(rho, t + y)
                    r = q / formula
                    require(1 / math.sqrt(2) * (1 - TOL) <= r <= 2 * (1 + TOL), f"Q bounds fail ({r}), " + where)
                    extremes["min Q/R_formula"] = min(extremes["min Q/R_formula"], r)
                    extremes["max Q/R_formula"] = max(extremes["max Q/R_formula"], r)
                    if 1.5 <= alpha <= 3:
                        tr = t / (x * math.sqrt(rho * p))
                        require(tr <= 4.13, f"window tail bound fails ({tr}), " + where)
                        w = formula / min(rho, y)
                        require(1 - TOL <= w <= 5.13, f"window formula fails ({w}), " + where)
                        extremes["max T/(x sqrt(rho Phi)), window"] = max(
                            extremes["max T/(x sqrt(rho Phi)), window"], tr)
                        extremes["min R_formula/min(rho,Y), window"] = min(
                            extremes["min R_formula/min(rho,Y), window"], w)
                        extremes["max R_formula/min(rho,Y), window"] = max(
                            extremes["max R_formula/min(rho,Y), window"], w)
                if 1.5 <= alpha <= 3:                        # saturated side: x >= rho^(1/alpha)
                    y = s * math.sqrt(rho * p * (1 + math.log(n)))
                    require(y >= 0.72 * rho, f"saturation bound fails ({y / rho}), " + where)
    return extremes


def main() -> int:
    rng = random.Random(20261109)
    for title, extremes in (("Part A: finite laws", part_a(rng)), ("Part B: power laws", part_b(rng))):
        print(title)
        for name, value in extremes.items():
            print(f"  {name}: {value:.6f}")
    if FAILURES:
        print(f"{len(FAILURES)} FAILURES")
        for failure in FAILURES[:10]:
            print("  " + failure)
        return 1
    print("All checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
