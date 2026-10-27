"""Exact finite-prefix checks of the Hellinger midpoint decomposition.

No Monte Carlo and no optimization are used. Probabilities and work use
Fraction arithmetic. Square roots are enclosed by exact dyadic rationals,
whose squared endpoints are checked. These finite atomic examples validate
identities and implementation sanity; they do not prove the continuum-law
entropy bound, the simultaneous hard pair, or an unrestricted minimax law.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path


ROOT_BITS = 160
CASES = (
    {
        "name": "two_scales",
        "gaps": (F(1, 4), F(1, 16)),
        "masses": (F(16, 17), F(1, 17)),
        "minus": (F(1, 64), F(1, 4)),
        "plus": (F(1, 16), F(1, 2)),
        "rho": F(1, 8),
    },
    {
        "name": "three_scales",
        "gaps": (F(1, 4), F(1, 8), F(1, 32)),
        "masses": (F(64, 81), F(16, 81), F(1, 81)),
        "minus": (F(0), F(1, 16), F(1, 2)),
        "plus": (F(1, 32), F(1, 4), F(1, 2)),
        "rho": F(1, 8),
    },
)


def rat(x: F) -> str:
    return str(x)


def interval(lo: F, hi: F) -> dict:
    assert lo <= hi
    return {"lower": rat(lo), "upper": rat(hi), "midpoint_float": float((lo + hi) / 2)}


@lru_cache(maxsize=None)
def root_bounds(x: F) -> tuple[F, F]:
    assert x >= 0
    root_num, root_den = math.isqrt(x.numerator), math.isqrt(x.denominator)
    if root_num * root_num == x.numerator and root_den * root_den == x.denominator:
        exact = F(root_num, root_den)
        return exact, exact
    scale = 1 << ROOT_BITS
    k = math.isqrt((x.numerator * scale * scale) // x.denominator)
    lo = F(k, scale)
    hi = lo if lo * lo == x else F(k + 1, scale)
    assert lo * lo <= x <= hi * hi
    return lo, hi


def hsquared(p: list[F], q: list[F]) -> tuple[F, F]:
    assert len(p) == len(q)
    assert sum(p) == sum(q) == 1
    alo = ahi = F(0)
    for x, y in zip(p, q):
        lo, hi = root_bounds(x * y)
        alo += lo
        ahi += hi
    return max(F(0), 1 - ahi), max(F(0), 1 - alo)


def choose(policy: str, words: tuple[tuple[int, ...], ...], bits: tuple[int, ...], last: int) -> int | None:
    t = len(bits)
    if policy == "zero":
        return None
    if policy == "fresh":
        return len(words)
    if policy == "single":
        return 0
    if policy == "screen":
        if t >= 3 and bits[-2:] == (0, 0):
            return None
        return last if t and bits[-1] else len(words)
    assert policy == "interleave"
    if not t:
        return 0
    if t == 1:
        return 0 if bits[0] else 1
    if t >= 4 and bits[-3:] == (0, 0, 0):
        return None
    if t % 3 == 0:
        return len(words)
    if bits[-1]:
        return min(range(len(words)), key=lambda i: (len(words[i]), i))
    return (last + 1) % len(words)


def leaves(policy: str, cap: int):
    """Canonical first-observation indexing; every leaf is an ordered history."""
    out = []

    def visit(words=(), bits=(), last=0, actions=()):
        i = None if len(bits) == cap else choose(policy, words, bits, last)
        if i is None:
            out.append((words, bits, actions))
            return
        assert 0 <= i <= len(words)
        for b in (0, 1):
            w = list(words)
            if i == len(w):
                w.append(())
            w[i] = w[i] + (b,)
            visit(tuple(w), bits + (b,), i, actions + (i,))

    visit()
    assert len({bits for _, bits, _ in out}) == len(out)
    return out


def mixture(policy: str):
    if policy == "mixed":
        return (("zero", F(1, 5)), ("interleave", F(2, 5)), ("fresh", F(1, 5)), ("single", F(1, 5)))
    return ((policy, F(1)),)


def experiment(case, policy: str, cap: int) -> dict:
    d, mu = case["gaps"], case["masses"]
    qm, qp = case["minus"], case["plus"]
    qb = tuple((x + y) / 2 for x, y in zip(qm, qp))
    qzero = tuple(F(0) for _ in d)
    assert sum(mu) == 1
    for q in (qm, qp, qb):
        assert all(0 <= x <= F(1, 2) for x in q)
        assert sum(m * x for m, x in zip(mu, q)) <= case["rho"]

    @lru_cache(maxsize=None)
    def wordprob(word, q):
        h, t = sum(word), len(word)
        return sum(
            mass * ((1 - qi) * (F(1, 2) - gap) ** h * (F(1, 2) + gap) ** (t - h)
                    + qi * (F(1, 2) + gap) ** h * (F(1, 2) - gap) ** (t - h))
            for gap, mass, qi in zip(d, mu, q)
        )

    def product(xs):
        result = F(1)
        for x in xs:
            result *= x
        return result

    rows = []
    for seed, weight in mixture(policy):
        for words, bits, actions in leaves(seed, cap):
            padded = words + ((),) * (cap - len(words))
            pm = [wordprob(w, qm) for w in padded]
            pp = [wordprob(w, qp) for w in padded]
            pb = [wordprob(w, qb) for w in padded]
            p0 = [wordprob(w, qzero) for w in padded]
            assert all(b == (m + p) / 2 for b, m, p in zip(pb, pm, pp))
            assert all(z <= 2 * b for z, b in zip(p0, pb))
            rows.append({
                "seed": seed, "weight": weight, "words": padded, "bits": bits,
                "minus": weight * product(pm), "plus": weight * product(pp),
                "mid": weight * product(pb),
                "hybrid_minus": [weight * pm[i] * product(pb[j] for j in range(cap) if j != i) for i in range(cap)],
                "hybrid_plus": [weight * pp[i] * product(pb[j] for j in range(cap) if j != i) for i in range(cap)],
                "hybrid_zero": [weight * p0[i] * product(pb[j] for j in range(cap) if j != i) for i in range(cap)],
            })

    for label in ("minus", "plus", "mid"):
        assert sum(r[label] for r in rows) == 1
    for i in range(cap):
        for label in ("hybrid_minus", "hybrid_plus", "hybrid_zero"):
            assert sum(r[label][i] for r in rows) == 1

    hpop = hsquared([r["minus"] for r in rows], [r["plus"] for r in rows])
    hybrids = [hsquared([r["hybrid_minus"][i] for r in rows], [r["hybrid_plus"][i] for r in rows]) for i in range(cap)]
    slo = sum((h[0] for h in hybrids), F(0))
    shi = sum((h[1] for h in hybrids), F(0))
    # For cap zero equality is rational. All positive-cap selected examples
    # have a strict decomposition gap large enough for these exact enclosures.
    assert hpop[1] <= slo
    wm = [sum(r["mid"] * len(r["words"][i]) for r in rows) for i in range(cap)]
    w0 = [sum(r["hybrid_zero"][i] * len(r["words"][i]) for r in rows) for i in range(cap)]
    assert all(x <= 2 * y for x, y in zip(w0, wm))
    totalwork = sum(r["mid"] * len(r["bits"]) for r in rows)
    assert sum(wm) == totalwork <= cap
    for r in rows:
        assert all(r["hybrid_zero"][i] <= 2 * r["mid"] for i in range(cap))
    return {
        "case": case["name"], "policy": policy, "cap": cap,
        "revealed_seed_leaf_count": len(rows),
        "theta_minus": rat(sum(x * y for x, y in zip(mu, qm))),
        "theta_plus": rat(sum(x * y for x, y in zip(mu, qp))),
        "population_h": interval(*hpop),
        "sum_hybrid_h": interval(slo, shi),
        "decomposition_gap_lower": rat(slo - hpop[1]),
        "null_hybrid_slot_work": list(map(rat, w0)),
        "midpoint_slot_work": list(map(rat, wm)),
        "midpoint_total_work": rat(totalwork),
        "normalization_exact": True,
        "midpoint_word_affinity_exact": True,
        "hellinger_decomposition_certified": True,
        "null_cost_domination_exact": True,
        "work_sum_exact": True,
    }


def sufficient_statistic_check(case, cap=5):
    """Check population-independent conditional seed/word given(T,heads)."""
    d, mu = case["gaps"], case["masses"]
    qs = (case["minus"], case["plus"])
    rows = []
    for seed, weight in ((0, F(1, 5)), (1, F(1, 3)), (2, F(7, 15))):
        def visit(bits=()):
            stop = seed == 0 or len(bits) == cap or (seed == 1 and len(bits) >= 2 and bits[-1] == 1)
            if stop:
                t, h = len(bits), sum(bits)
                probs = []
                for q in qs:
                    probs.append(weight * sum(m * ((1 - qi) * (F(1, 2) - gap) ** h * (F(1, 2) + gap) ** (t - h)
                                          + qi * (F(1, 2) + gap) ** h * (F(1, 2) - gap) ** (t - h))
                                              for gap, m, qi in zip(d, mu, q)))
                rows.append((seed, bits, (t, h), probs))
            else:
                visit(bits + (0,))
                visit(bits + (1,))
        visit()
    groups = {}
    for _, _, stat, probs in rows:
        v = groups.setdefault(stat, [F(0), F(0)])
        v[0] += probs[0]
        v[1] += probs[1]
    assert all(sum(r[3][j] for r in rows) == 1 for j in (0, 1))
    for _, _, stat, probs in rows:
        assert probs[0] / groups[stat][0] == probs[1] / groups[stat][1]
    # This rational equality establishes the exact common conditional kernel;
    # Hellinger equality follows without subtracting approximate roots.
    return {"case": case["name"], "cap": cap, "full_seed_word_atoms": len(rows),
            "statistic_atoms": len(groups), "conditional_kernel_independent_exact": True,
            "affinity_preserved_exact_via_common_conditional_kernel": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("check_prefix_results.json"))
    args = parser.parse_args()
    results = []
    for case in CASES:
        for policy in ("interleave", "screen", "mixed"):
            for cap in (2, 4, 6):
                results.append(experiment(case, policy, cap))
        results.append(experiment(case, "mixed", 0))
    sanity = [sufficient_statistic_check(case) for case in CASES]
    output = {
        "status": "finite_exact_checks_passed",
        "scope": "finite atomic observable trees only; not proof of continuum or all-policy theorem",
        "arithmetic": "Fraction probabilities/work and certified dyadic square-root enclosures",
        "sqrt_bits": ROOT_BITS, "monte_carlo": False, "random_seed": None,
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "population_cases": len(results), "sufficiency_cases": len(sanity),
        "results": results, "sufficiency": sanity,
    }
    args.output.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": output["status"], "population_cases": len(results),
                      "sufficiency_cases": len(sanity), "output": str(args.output)}))


if __name__ == "__main__":
    main()
