"""Exact full-Q_rho deterministic-cap-two feedback certificate.

Uses only Fraction arithmetic. Floating point appears solely in display
fields. The design prior was fixed after a 30-step rational exploratory
bisection; its optimality is neither assumed nor needed.
"""
from fractions import Fraction as F
import json
from pathlib import Path

RHO = F(1, 4)
PRIOR = F(1074499095, 2147483648)
VERTICES = ((F(0), F(0)), (F(1, 32), RHO), (F(1, 16), RHO))
UPPER = F(15443, 1000000)
LOWER = F(15475, 1000000)


def trim(p):
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def add(p, q):
    return trim([(p[i] if i < len(p) else F(0)) +
                 (q[i] if i < len(q) else F(0)) for i in range(max(len(p), len(q)))])


def scale(p, s):
    return trim([s*x for x in p])


def mul(p, q):
    r = [F(0)]*(len(p)+len(q)-1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i+j] += a*b
    return trim(r)


def evaluate(p, x):
    return sum(c*x**i for i, c in enumerate(p))


def second_derivative(p):
    return trim([F(i*(i-1))*p[i] for i in range(2, len(p))] or [F(0)])


def display(x):
    return {"fraction": str(x), "decimal_display": float(x)}


def certify():
    # A = E[Dq(D)]. Word order is TT, TH, HT, HH.
    head = [F(5, 16), F(2)]
    tail = [F(11, 16), F(-2)]
    old = [[F(61, 128), F(-2)], [F(27, 128)],
           [F(27, 128)], [F(13, 128), F(2)]]
    new = [mul(tail, tail), mul(tail, head), mul(head, tail), mul(head, head)]
    adaptive = new[:2] + old[2:]
    for law in (old, new, adaptive):
        total = [F(0)]
        for cell in law:
            total = add(total, cell)
        assert total == [F(1)]

    a = [evaluate(cell, F(0)) for cell in adaptive]
    b = [evaluate(cell, F(1, 32)) for cell in adaptive]
    outputs = [RHO*PRIOR*y/((1-PRIOR)*x+PRIOR*y) for x, y in zip(a, b)]
    assert all(0 < y < RHO for y in outputs)

    def edge_risk(theta):
        risk = [F(0)]
        for cell, output in zip(adaptive, outputs):
            error = add([output], scale(theta, -1))
            risk = add(risk, mul(cell, mul(error, error)))
        return risk

    edges = (
        ("q2_zero_theta_4A", [F(0), F(4)], F(0), F(1, 16)),
        ("q1_zero_theta_8A", [F(0), F(8)], F(0), F(1, 32)),
        ("rarity_boundary_theta_rho", [RHO], F(1, 32), F(1, 16)),
    )
    edge_results = []
    for (name, theta, lo, hi), simple_curvature_lower in zip(edges, (F(30), F(124), F(3, 100))):
        risk = edge_risk(theta)
        derivative = second_derivative(risk)
        assert len(risk) <= 4  # degree <= 3, so second derivative is affine
        values = [evaluate(derivative, endpoint) for endpoint in (lo, hi)]
        assert min(values) > simple_curvature_lower > 0
        edge_results.append({"name": name, "interval": [str(lo), str(hi)],
                             "risk_coefficients_ascending": [str(x) for x in risk],
                             "second_derivative_coefficients_ascending": [str(x) for x in derivative],
                             "second_derivative_at_endpoints": [display(x) for x in values],
                             "simple_second_derivative_lower_bound": str(simple_curvature_lower),
                             "strictly_convex_on_edge": True})

    def risk_at(A, theta):
        return sum(evaluate(cell, A)*(y-theta)**2 for cell, y in zip(adaptive, outputs))

    vertex_risks = [risk_at(A, theta) for A, theta in VERTICES]
    worst_upper = max(vertex_risks)
    bayes_lower = {}
    for name, law in (("same_coin", old), ("two_fresh", new)):
        p0 = [evaluate(cell, F(0)) for cell in law]
        p1 = [evaluate(cell, F(1, 32)) for cell in law]
        assert min(p0+p1) > 0 and sum(p0) == sum(p1) == 1
        value = RHO**2*PRIOR*(1-PRIOR)*sum(
            x*y/((1-PRIOR)*x+PRIOR*y) for x, y in zip(p0, p1))
        bayes_lower[name] = value
    best_lower = min(bayes_lower.values())
    assert worst_upper < UPPER < LOWER < best_lower
    return {
        "evidence_status": "PROVED-ON-PAPER plus exact rational full-class certificate",
        "arithmetic": "fractions.Fraction; decimal displays are noncertifying",
        "rho": str(RHO), "mu_atoms": ["1/4", "1/8"], "mu_weights": ["1/2", "1/2"],
        "class": "ALL q1,q2>=0 with q1+q2<=1/2",
        "budget": "deterministic total cap TWO; NOT expected-budget-two comparison",
        "prior_probability_hard_alternative": str(PRIOR),
        "hard_alternative": {"q1": "0", "q2": "1/2"},
        "null": {"q1": "0", "q2": "0"},
        "word_order": ["TT", "TH", "HT", "HH"],
        "adaptive_output_table": [str(x) for x in outputs],
        "adaptive_probability_polynomials_in_A": [[str(x) for x in cell] for cell in adaptive],
        "theta_convexity": "second derivative exactly 2, for every fixed A",
        "edge_certificates": edge_results,
        "vertices_A_theta": [[str(x) for x in vertex] for vertex in VERTICES],
        "vertex_risks": [display(x) for x in vertex_risks],
        "full_class_adaptive_upper": display(worst_upper),
        "fixed_schedule_bayes_lower": {name: display(x) for name, x in bayes_lower.items()},
        "noninteractive_full_class_lower": display(best_lower),
        "certified_minimax_gap": display(best_lower-worst_upper),
        "simple_upper": str(UPPER), "simple_lower": str(LOWER),
        "simple_gap": str(LOWER-UPPER), "all_exact_checks_pass": True,
    }


if __name__ == "__main__":
    result = certify()
    target = Path(__file__).with_name("full_class_certificate.json")
    target.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print("PASS: full global-rarity triangle; exact convex-edge and minimax-gap certificate")
