"""Exact finite-prefix diagnostics for the asymmetric classifier.

All probabilities in the finite experiments use Fraction, without Monte Carlo.
The cap is explicit: unresolved probability is reported, not discarded or
classified. These checks do not prove infinite-horizon or all-algorithm claims.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import math

HERE = Path(__file__).resolve().parent


def table(a, rho, epsilon, cap):
    """Actions at (n,heads), with exact rational likelihood comparisons.

    A detector can be omitted when even an all-favorable path cannot cross
    its smaller boundary by the current n. All omitted indices are checked
    by monotonicity: smaller r and larger boundary only make crossing harder.
    """
    actions = {}
    max_active = 0
    for n in range(1, cap + 1):
        active = []
        for k in range(n):
            r = a / 2 ** (k + 1)
            boundary = 2 ** (k + 1) / epsilon
            if (1 + 2*r) ** n < boundary:
                break
            active.append((r, boundary))
        max_active = max(max_active, len(active))
        for h in range(n + 1):
            action = None
            for r, boundary in active:
                plus = (1 + 2*r) ** h * (1 - 2*r) ** (n - h)
                minus = (1 - 2*r) ** h * (1 + 2*r) ** (n - h)
                # Fixed negative-first convention; the proof does not rely on ties.
                if minus >= boundary:
                    action = 0
                    break
                if plus >= boundary / rho:
                    action = 1
                    break
            actions[n, h] = action
    return actions, max_active


def exact_prefix(p, actions, cap):
    alive = {0: F(1)}
    decisions = [F(0), F(0)]
    work = F(0)
    for n in range(1, cap + 1):
        work += sum(alive.values())
        nxt = {}
        for heads, mass in alive.items():
            for bit, probability in [(0, 1-p), (1, p)]:
                h = heads + bit
                value = mass * probability
                action = actions[n, h]
                if action is None:
                    nxt[h] = nxt.get(h, F(0)) + value
                else:
                    decisions[action] += value
        alive = nxt
    unresolved = sum(alive.values(), F(0))
    assert sum(decisions) + unresolved == 1
    return decisions, unresolved, work


def encoded(x):
    return dict(fraction=str(x), decimal=float(x))


def main():
    rows = []
    cap = 80
    for rho, epsilon in [(F(1, 4), F(1, 16)), (F(1, 64), F(1, 16)),
                         (F(1, 4), F(1, 256))]:
        actions, active = table(F(1, 2), rho, epsilon, cap)
        for d in [F(1, 2), F(1, 4), F(1, 16)]:
            for sign in [0, 1]:
                p = F(1, 2) + (2*sign-1)*d
                decisions, unresolved, work = exact_prefix(p, actions, cap)
                error = decisions[1-sign]
                limit = epsilon if sign else rho*epsilon
                assert error <= limit
                rows.append(dict(a="1/2", rho=str(rho), epsilon=str(epsilon),
                                 d=str(d), sign=sign, cap=cap,
                                 finite_prefix_error=encoded(error),
                                 error_bound=str(limit), unresolved=encoded(unresolved),
                                 expected_min_T_cap=encoded(work), max_active=active))
    # Exact single-term moment summation, including the analytic geometric tail.
    base = F(17, 16) / F(1, 2)
    increment_series = F(17, 4) * F(1, 8) / (1-F(1, 8))
    moment = base + increment_series
    assert moment == F(153, 56) < 3
    # Numerical displays of analytic constants; these are not optimized bounds.
    constants = []
    for alpha in [2.01, 2.1, 3., 4., 8.]:
        beta = 1-2/alpha
        a0, a1 = alpha/(alpha-2), alpha/(alpha-2)**2
        w = 1.5*(a0*(1+10*math.log(2)+1/(math.e*beta))+a1)
        constants.append(dict(alpha=alpha, work_coefficient=w,
                              rms_coefficient=math.sqrt(3*w)))
    result = dict(status="numerical evidence; exact rational finite-prefix diagnostics",
                  seed=None, sampling="none; exact dynamic programming over all paths",
                  limitation="Cap 80; unresolved mass is retained. No infinite-time numerical claim.",
                  second_moment_coefficient=str(moment), rows=rows, constants=constants)
    (HERE / "construction-checks.json").write_text(json.dumps(result, indent=2)+"\n")
    print(f"Passed {len(rows)} exact finite-prefix experiments; unresolved tails retained.")
    print(f"Exact analytic moment-series coefficient: {moment} < 3.")
    print("No held-out samples, optimization, or statistical confidence claims.")


if __name__ == "__main__":
    main()
