"""Rational arithmetic checks for the paper-only 713 upper bound."""
from fractions import Fraction as F
from math import factorial
import json
from pathlib import Path

r = F(442, 625)
assert 2 * r**2 > 1  # 1/sqrt(2) < r.
c0 = 1/(1-r) * (1/(1-r) + 1/(1-r**3))
assert c0 < 17
assert F(4, 3)**4 > 3
assert F(68, 3) < 23
assert sum(F(2)**k/factorial(k) for k in range(6)) > 7
assert sum(F(1, 2)**k/factorial(k) for k in range(3)) > F(8, 5)
assert F(1, 7) + F(5, 12) < F(3, 5)
assert F(125, 18) < 7 and F(338, 49) < 7
assert 2 * F(71, 100)**2 > 1
assert sum(F(7, 10)**k/factorial(k) for k in range(5)) > 2
work = 7 * (2 + F(70, 29))
assert work < 31
out = {"status": "arithmetic checks only; full argument is a paper proof",
       "candidate": {"k1": .25, "k2": 1.}, "c0_rational_upper": str(c0),
       "second_moment_constant": 23, "work_constant": 31,
       "work_rational_upper": str(work), "uniform_product_constant": 23*31,
       "all_checks_passed": True}
root = Path(__file__).resolve().parents[2]
(root / "results/constants_uniform_bound.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
