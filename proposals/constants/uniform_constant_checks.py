"""Rational arithmetic checks for the paper-only 713 upper bound."""
from fractions import Fraction as F
from math import factorial
import json
from pathlib import Path


def require(condition, message):
    # Explicit checks, unlike assert, still run under python -O.
    if not condition:
        raise RuntimeError(message)


r = F(442, 625)
require(2 * r**2 > 1, "r does not exceed 1/sqrt(2)")  # 1/sqrt(2) < r.
c0 = 1/(1-r) * (1/(1-r) + 1/(1-r**3))
require(c0 < 17, "c0 bound fails")
require(F(4, 3)**4 > 3, "(4/3)^4 > 3 fails")
require(F(68, 3) < 23, "68/3 < 23 fails")
require(sum(F(2)**k/factorial(k) for k in range(6)) > 7, "exp(2) series bound fails")
require(sum(F(1, 2)**k/factorial(k) for k in range(3)) > F(8, 5), "exp(1/2) series bound fails")
require(F(1, 7) + F(5, 12) < F(3, 5), "1/7 + 5/12 < 3/5 fails")
require(F(125, 18) < 7 and F(338, 49) < 7, "125/18 and 338/49 bounds fail")
require(2 * F(71, 100)**2 > 1, "0.71 does not exceed 1/sqrt(2)")
require(sum(F(7, 10)**k/factorial(k) for k in range(5)) > 2, "exp(7/10) series bound fails")
work = 7 * (2 + F(70, 29))
require(work < 31, "work bound fails")
out = {"status": "arithmetic checks only; full argument is a paper proof",
       "candidate": {"k1": .25, "k2": 1.}, "c0_rational_upper": str(c0),
       "second_moment_constant": 23, "work_constant": 31,
       "work_rational_upper": str(work), "uniform_product_constant": 23*31,
       "all_checks_passed": True}
root = Path(__file__).resolve().parents[2]
(root / "results/constants_uniform_bound.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
