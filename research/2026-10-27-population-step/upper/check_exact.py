"""Enumerate finite transcripts with rational arithmetic; not minimax numerics."""

from datetime import datetime, timezone
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json
import platform

from two_gap_control import estimate_with_pilot, features, specification

HERE = Path(__file__).resolve().parent
TAPES = list(product((0, 1), repeat=3))


def tape_law(spec, q):
    result = []
    for tape in TAPES:
        h = sum(tape)
        probability = F(0)
        for d, mass, positive in zip(
            (spec["d1"], spec["d2"]),
            (spec["mass1"], 1 - spec["mass1"]),
            q,
        ):
            pminus, pplus = F(1, 2) - d, F(1, 2) + d
            probability += mass * (
                positive * pplus**h * (1 - pplus) ** (3 - h)
                + (1 - positive) * pminus**h * (1 - pminus) ** (3 - h)
            )
        y, z = features(tape, spec)
        result.append((probability, y, z))
    assert sum(p for p, y, z in result) == 1
    return result


def verify_case(name, d1, d2, mass1, rho, q):
    spec = specification(d1, d2, mass1)
    q = tuple(map(F, q))
    theta = mass1 * q[0] + (1 - mass1) * q[1]
    assert 0 <= theta <= rho <= F(1, 4)
    law = tape_law(spec, q)
    m1 = sum(m * (2 * s - 1) * (2 * d) for m, d, s in zip(
        (mass1, 1 - mass1), (d1, d2), q))
    m3 = sum(m * (2 * s - 1) * (2 * d) ** 3 for m, d, s in zip(
        (mass1, 1 - mass1), (d1, d2), q))
    a, b, m2, v = (spec[key] for key in ("a", "b", "m2", "v"))
    K = a * a * (1 + 2 * m2) / 3 + 2 * a * b * m2 + b * b
    variance = K - F(1, 4) + theta - theta * theta
    covariance = a * ((F(2, 3) - m2) * m1 + m3 / 3) + b * (m1 - m2 * m3)
    yz_variance = sum(p * (y * z - covariance) ** 2 for p, y, z in law)
    assert sum(p * y for p, y, z in law) == theta
    assert sum(p * z for p, y, z in law) == 0
    assert sum(p * z * z for p, y, z in law) == v
    assert sum(p * (y - theta) ** 2 for p, y, z in law) == variance
    assert sum(p * y * z for p, y, z in law) == covariance
    assert variance * v >= covariance * covariance

    enumerated = []
    for pilot_count, production_count in ((1, 1), (2, 1), (1, 2)):
        mse = F(0)
        mean = F(0)
        clipped_mse = F(0)
        total_probability = F(0)
        transcript_count = 0
        for outcomes in product(law, repeat=pilot_count + production_count):
            probability = F(1)
            for p, y, z in outcomes:
                probability *= p
            if not probability:
                continue
            transcript_count += 1
            beta = sum(y * z for p, y, z in outcomes[:pilot_count]) / (pilot_count * v)
            raw = sum(y - beta * z for p, y, z in outcomes[pilot_count:]) / production_count
            clipped = min(rho, max(F(0), raw))
            total_probability += probability
            mean += probability * raw
            mse += probability * (raw - theta) ** 2
            clipped_mse += probability * (clipped - theta) ** 2
        prediction = (variance - covariance * covariance / v + yz_variance / (pilot_count * v)) / production_count
        assert total_probability == 1
        assert mean == theta
        assert mse == prediction
        assert clipped_mse <= mse
        enumerated.append(dict(pilot_coins=pilot_count, production_coins=production_count,
            nonzero_transcripts=transcript_count, mean=str(mean), mse=str(mse),
            formula_mse=str(prediction), clipped_mse=str(clipped_mse),
            flips=3 * (pilot_count + production_count)))
    return dict(name=name, d1=str(d1), d2=str(d2), mass1=str(mass1), rho=str(rho),
        q=list(map(str, q)), theta=str(theta), a=str(a), b=str(b),
        v=str(v), variance=str(variance), covariance=str(covariance),
        yz_variance=str(yz_variance), finite_transcript_checks=enumerated)


def verify_interface():
    spec = specification(F(1, 8), F(1, 4), F(1, 2))
    tapes = [(0, 1, 0), (1, 1, 0), (0, 0, 0)]
    state = {"coins": 0, "flips": 0}

    def factory():
        tape = iter(tapes[state["coins"]])
        state["coins"] += 1

        def flip():
            state["flips"] += 1
            return next(tape)

        return flip

    result = estimate_with_pilot(factory, spec, 1, 2, F(1, 4))
    assert state == {"coins": 3, "flips": 9}
    assert result["fresh_coins"] == 3 and result["flips"] == 9
    y0, z0 = features(tapes[0], spec)
    beta = y0 * z0 / spec["v"]
    expected = sum(y - beta * z for y, z in [features(t, spec) for t in tapes[1:]]) / 2
    assert result["raw"] == expected
    return {key: str(value) for key, value in result.items()}


def main():
    cases = []
    for name, q in (
        ("zero", (F(0), F(0))),
        ("independent_boundary", (F(1, 4), F(1, 4))),
        ("all_positive_mass_at_small_gap", (F(1, 2), F(0))),
        ("all_positive_mass_at_large_gap", (F(0), F(1, 2))),
    ):
        cases.append(verify_case(name, F(1, 8), F(1, 4), F(1, 2), F(1, 4), q))
    cases.append(verify_case("endpoint_and_rare_difficult_subpopulation",
        F(1, 32), F(1, 2), F(1, 16), F(1, 8), (F(1), F(1, 15))))
    cases.append(verify_case("widely_separated_tiny_rarity",
        F(1, 128), F(3, 8), F(1, 64), F(1, 64), (F(1), F(0))))
    payload = {
        "status": "EXACT_RATIONAL_FINITE_CHECKS_PASSED",
        "scope": "Finite moment and finite pilot/production identities; no minimax numerical certificate",
        "utc": datetime.now(timezone.utc).isoformat(),
        "python_version": platform.python_version(),
        "arithmetic": "Python fractions.Fraction, exact rational; no seeds or Monte Carlo",
        "source_sha256": {name: hashlib.sha256((HERE / name).read_bytes()).hexdigest()
            for name in ("check_exact.py", "two_gap_control.py", "proof.tex", "RESULT.md")},
        "cases": cases,
        "interface_check": verify_interface(),
    }
    out = HERE / "exact_checks.json"
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {len(cases)} rational laws, 18 finite transcript checks, interface accounting")
    print(out)


if __name__ == "__main__":
    main()
