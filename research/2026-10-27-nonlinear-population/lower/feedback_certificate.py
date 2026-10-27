"""Exact finite-experiment certificates; no floating-point optimization.

The three dyadic priors were selected by a 30-step rational bisection in an
exploratory command, then fixed here before certification. Every inequality
below is checked by Python Fraction arithmetic. Decimal fields are display
only. This certifies a two-observation model, not an unrestricted minimax rate.
"""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path

RHO = F(1, 4)
WORDS = tuple(product((0, 1), repeat=2))
CASES = (
    ("gap_ratio_2", F(1, 8), F(1075683009, 2147483648), F(7623, 500000), F(15313, 1000000)),
    ("gap_ratio_16", F(1, 64), F(1074086023, 2147483648), F(15459, 1000000), F(15482, 1000000)),
    ("gap_ratio_256", F(1, 1024), F(1073999895, 2147483648), F(15480, 1000000), F(15497, 1000000)),
)
POLICIES = {
    "same_coin": ("old", "old"),
    "two_fresh": ("new", "new"),
    "tail_fresh_head_revisit": ("new", "old"),
    "tail_revisit_head_fresh": ("old", "new"),
}


def encode(value):
    return {"fraction": str(value), "decimal_display": float(value)}


def certify(name, small_gap, prior, upper, lower):
    gaps = (F(1, 4), small_gap)

    def word_prob(word, hypothesis):
        heads, n = sum(word), len(word)
        q = RHO if hypothesis else F(0)
        return sum(
            F(1, 2) * (
                (1 - q) * (F(1, 2) - d)**heads * (F(1, 2) + d)**(n-heads)
                + q * (F(1, 2) + d)**heads * (F(1, 2) - d)**(n-heads)
            ) for d in gaps
        )

    def evaluate(policy):
        probabilities = [
            [word_prob((x, y), h) if policy[x] == "old" else
             word_prob((x,), h) * word_prob((y,), h) for x, y in WORDS]
            for h in (0, 1)
        ]
        assert all(sum(ps) == 1 and min(ps) > 0 for ps in probabilities)
        estimates = [
            RHO * prior * p1 / ((1-prior)*p0 + prior*p1)
            for p0, p1 in zip(*probabilities)
        ]
        assert all(0 < y < RHO for y in estimates)
        risks = [sum(p*(y-h*RHO)**2 for p, y in zip(ps, estimates))
                 for h, ps in enumerate(probabilities)]
        bayes = (1-prior)*risks[0] + prior*risks[1]
        # Independent formula: posterior conditional variance summed over cells.
        bayes_variance = sum(
            RHO**2 * prior*(1-prior)*p0*p1 / ((1-prior)*p0 + prior*p1)
            for p0, p1 in zip(*probabilities)
        )
        assert bayes == bayes_variance
        return probabilities, estimates, risks, bayes

    results = {key: evaluate(policy) for key, policy in POLICIES.items()}
    adaptive_upper = max(results["tail_fresh_head_revisit"][2])
    noninteractive_lower = min(results[key][3] for key in ("same_coin", "two_fresh"))
    assert adaptive_upper < upper < lower < noninteractive_lower
    assert adaptive_upper < noninteractive_lower
    return {
        "name": name, "rho": str(RHO), "magnitude_atoms": [str(d) for d in gaps],
        "magnitude_weights": ["1/2", "1/2"], "hypotheses": ["q(d)=0", "q(d)=1/4"],
        "prior_probability_hypothesis_1": str(prior), "charged_flips": 2,
        "budget_type": "deterministic cap; no expected-budget comparison",
        "policies": {
            key: {"action_after_tail": POLICIES[key][0], "action_after_head": POLICIES[key][1],
                  "word_order": [list(word) for word in WORDS],
                  "word_probabilities": [[str(p) for p in ps] for ps in value[0]],
                  "posterior_mean_outputs": [str(y) for y in value[1]],
                  "conditional_mse": [encode(v) for v in value[2]],
                  "bayes_mse": encode(value[3])}
            for key, value in results.items()
        },
        "adaptive_minimax_upper": encode(adaptive_upper),
        "noninteractive_minimax_lower": encode(noninteractive_lower),
        "certified_separation": encode(noninteractive_lower-adaptive_upper),
        "simple_upper": str(upper), "simple_lower": str(lower),
        "simple_gap": str(lower-upper), "all_exact_inequalities_pass": True,
    }


if __name__ == "__main__":
    result = {
        "status": "DISPROVED fixed-schedule equivalence; exact rational finite experiment",
        "arithmetic": "Python fractions.Fraction; decimals are noncertifying display fields",
        "seed": None,
        "cases": [certify(*case) for case in CASES],
    }
    target = Path(__file__).with_name("feedback_certificate.json")
    target.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {len(result['cases'])} exact rational minimax-separation certificates")
