"""Exact polynomial and finite feedback checks, not an unrestricted minimax DP."""

from datetime import datetime, timezone
from fractions import Fraction as F
from itertools import product
from math import comb, factorial
from pathlib import Path
import hashlib
import json
import platform

HERE = Path(__file__).resolve().parent


def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def add(p, q):
    return trim([(p[i] if i < len(p) else F(0)) + (q[i] if i < len(q) else F(0))
                 for i in range(max(len(p), len(q)))])


def scale(p, c):
    return trim([c * x for x in p])


def mul(p, q):
    ans = [F(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            ans[i + j] += x * y
    return trim(ans)


def power(p, n):
    ans = [F(1)]
    for _ in range(n):
        ans = mul(ans, p)
    return ans


def derivative(p):
    return trim([i * p[i] for i in range(1, len(p))] or [F(0)])


def integral01(p):
    return sum((c / (i + 1) for i, c in enumerate(p)), F(0))


def legendre(n):
    ans = [F(0)] * (n + 1)
    for j in range(n // 2 + 1):
        ans[n - 2 * j] = F((-1) ** j * factorial(2 * n - 2 * j),
            2**n * factorial(j) * factorial(n - j) * factorial(n - 2 * j))
    return ans


def u_polynomial(k):
    p = legendre(2 * k + 1)
    assert p[0] == 0 and p[1] != 0
    return scale(p[1:], 1 / p[1])


def verify_polynomial(k):
    p, u = legendre(2 * k + 1), u_polynomial(k)
    lam = 2 * k * (2 * k + 3)
    up = derivative(u)
    # The differential equation multiplied by x has no singular coefficient.
    ode = add(add(mul([F(0), F(1), F(0), F(-1)], derivative(up)),
                  mul([F(2), F(0), F(-4)], up)),
              scale(mul([F(0), F(1)], u), lam))
    assert ode == [0]
    energy = add(mul(u, u), scale(mul([F(1), F(0), F(-1)], mul(up, up)), F(1, lam)))
    left = scale(mul([F(0), F(1)], derivative(energy)), lam)
    right = mul([F(-4), F(0), F(6)], mul(up, up))
    assert left == right
    assert u[0] == 1 and energy[0] == 1
    assert sum(p) == 1 and abs(p[1]) >= 1
    assert sum(energy) == 1 / p[1] ** 2
    moments = [integral01([F(0)] * (2 * j + 2) + u) for j in range(k)]
    assert moments == [0] * k
    target_moment = integral01(scale([F(0)] + u, 2))
    assert target_moment == F(1, (k + 1) * (2 * k + 1))
    return dict(k=k, per_coin_cap=2 * k, coefficients=list(map(str, u)),
        target_moment=str(target_moment), energy_at_one=str(sum(energy)),
        ode_identity=True, energy_identity=True, moment_identities=True)


def word_probability(word, sign, k=2, a=F(1, 4), rho=F(1, 16)):
    # This rational test uses h=a sqrt(rho)=1/16. The theorem is not restricted
    # to square rational rho, but the finite arithmetic check is.
    assert a == F(1, 4) and rho == F(1, 16)
    h = F(1, 16)
    heads, tails = sum(word), len(word) - sum(word)
    minus = mul(power([F(1, 2), F(-1)], heads), power([F(1, 2), F(1)], tails))
    plus = mul(power([F(1, 2), F(1)], heads), power([F(1, 2), F(-1)], tails))
    # Integral of negative word likelihood over the full quadratic gap law.
    baseline = sum((2 * c * a**i / (i + 2) for i, c in enumerate(minus)), F(0))
    response = add(plus, scale(minus, -1))
    u = u_polynomial(k)
    q_scaled = scale(add([F(1)], scale(u, sign)), F(1, 2))
    correction = F(0)
    for i, c in enumerate(response):
        weighted_moment = integral01([F(0)] * (i + 1) + q_scaled)
        correction += 2 * c * h ** (i + 2) / (a * a) * weighted_moment
    return baseline + correction


def policy_action(words, global_bits):
    """Actual cross-coin feedback with cap4 and deterministic total horizon10.

    The first two observations use different coins. Thereafter the parity of
    all earlier heads decides whether to revisit an old coin or create a
    fresh one. Which old coin is revisited depends on all local head counts.
    This is a diagnostic acquisition policy, not a competitive estimator.
    """
    if len(global_bits) < 2:
        return len(words)
    eligible = [i for i, w in enumerate(words) if len(w) < 4]
    if sum(global_bits) % 2 and eligible:
        return max(eligible, key=lambda i: (sum(words[i]), -i))
    return len(words)


def feedback_check(horizon=10):
    probability_sum = F(0)
    two_point_mse = F(0)
    rho = F(1, 16)
    theta_plus, theta_minus = 8 * rho / 15, 7 * rho / 15
    midpoint = (theta_plus + theta_minus) / 2
    profile_choice_mse = [F(0), F(0)]
    for bits in product((0, 1), repeat=horizon):
        words = []
        prefix = []
        for bit in bits:
            action = policy_action(words, prefix)
            if action == len(words):
                words.append(())
            words[action] += (bit,)
            prefix.append(bit)
        assert all(len(w) <= 4 for w in words)
        probabilities = []
        for sign in (1, -1):
            value = F(1)
            for word in words:
                value *= word_probability(word, sign)
            probabilities.append(value)
        assert probabilities[0] == probabilities[1]
        probability = probabilities[0]
        probability_sum += probability
        two_point_mse += probability * (midpoint - theta_plus) ** 2
        # A literal pilot profile selector: use the first two bits to choose
        # a model, then report its target after feedback acquisition. Its
        # failure is deliberately retained, not tuned away.
        fitted_target = theta_plus if sum(bits[:2]) else theta_minus
        for j, theta in enumerate((theta_plus, theta_minus)):
            profile_choice_mse[j] += probability * (fitted_target - theta) ** 2
    assert probability_sum == 1
    assert two_point_mse == (rho / 30) ** 2
    assert max(profile_choice_mse) >= two_point_mse
    return dict(horizon=horizon, transcript_count=2**horizon,
        per_coin_cap=4, probabilities_identical=True, probability_sum=str(probability_sum),
        theta_plus=str(theta_plus), theta_minus=str(theta_minus),
        optimal_two_point_mse=str(two_point_mse),
        failed_profile_selector_mse=list(map(str, profile_choice_mse)),
        charged_flips=horizon)


def depth_tail_check(horizon=10):
    # K=1 gives indistinguishability through local depth2, but this actual
    # feedback algorithm is allowed depth4. Its terminal laws may differ.
    rho = F(1, 16)
    theta_plus, theta_minus = 7 * rho / 12, 5 * rho / 12
    delta = theta_plus - theta_minus
    exit_mass = [F(0), F(0)]
    total = [F(0), F(0)]
    risks = [F(0), F(0)]
    tv = F(0)
    common_mass = F(0)
    for bits in product((0, 1), repeat=horizon):
        words, prefix = [], []
        for bit in bits:
            action = policy_action(words, prefix)
            if action == len(words):
                words.append(())
            words[action] += (bit,)
            prefix.append(bit)
        probabilities = []
        for sign in (1, -1):
            value = F(1)
            for word in words:
                value *= word_probability(word, sign, k=1)
            probabilities.append(value)
        exited = max(map(len, words)) > 2
        for j in (0, 1):
            total[j] += probabilities[j]
            if exited:
                exit_mass[j] += probabilities[j]
        if not exited:
            assert probabilities[0] == probabilities[1]
            common_mass += probabilities[0]
        tv += abs(probabilities[0] - probabilities[1]) / 2
        # Posterior mean for this two-point finite diagnostic only.
        estimate = (probabilities[0] * theta_plus + probabilities[1] * theta_minus) / sum(probabilities)
        for j, theta in enumerate((theta_plus, theta_minus)):
            risks[j] += probabilities[j] * (estimate - theta) ** 2
    assert total == [1, 1]
    assert exit_mass[0] == exit_mass[1]
    p = exit_mass[0]
    assert common_mass == 1 - p
    assert tv <= p
    assert sum(risks) >= (1 - p) * delta**2 / 2
    necessity = 1 - 4 * max(risks) / delta**2
    assert p >= necessity
    assert horizon >= 3 * p
    return dict(k=1, horizon=horizon, actual_per_coin_cap=4,
        exit_probability_each=str(p), common_noexit_mass=str(common_mass),
        terminal_total_variation=str(tv), posterior_two_point_risks=list(map(str, risks)),
        exact_risk_depth_necessity=str(necessity), work_necessity=str(3 * p),
        scope="Finite diagnostic only; no certificate of unrestricted minimax risk")


def main():
    identities = [verify_polynomial(k) for k in range(1, 17)]
    word_count = 0
    for length in range(5):
        total = F(0)
        for word in product((0, 1), repeat=length):
            p = word_probability(word, 1)
            assert p == word_probability(word, -1)
            total += p
            word_count += 1
        assert total == 1
    output = dict(status="EXACT_RATIONAL_CHECKS_PASSED",
        scope="Polynomial identities K=1..16 and one finite feedback policy, not unrestricted minimax",
        utc=datetime.now(timezone.utc).isoformat(), python_version=platform.python_version(),
        arithmetic="Python fractions.Fraction; no floating point, seeds or Monte Carlo",
        polynomial_checks=identities, equal_local_words_checked=word_count,
        feedback_check=feedback_check(), depth_tail_check=depth_tail_check(),
        source_sha256={name: hashlib.sha256((HERE / name).read_bytes()).hexdigest()
            for name in ("proof.tex", "RESULT.md", "check_exact.py")})
    target = HERE / "exact_checks.json"
    target.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print("PASS: K=1..16 identities; 31 local words; 1024 capped and 1024 depth-tail feedback transcripts")
    print(target)


if __name__ == "__main__":
    main()
