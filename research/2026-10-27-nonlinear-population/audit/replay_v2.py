"""Second audit checkpoint: exact full-class feedback certificate and source closure.

Uses direct latent-mixture probabilities and rational interpolation, separately
from the author's polynomial implementation. No old result is overwritten.
The general approximation theorem is paper reviewed, not numerically proved.
"""
from datetime import datetime, timezone
from fractions import Fraction as F
from importlib.util import module_from_spec, spec_from_file_location
from itertools import product
from pathlib import Path
import hashlib
import json
import platform
import subprocess
import sys

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources():
    paths = ["lower/full_class.tex", "lower/full_class_certificate.py",
             "lower/full_class_certificate.json", "upper/FINITE_APPROXIMATION.tex",
             "audit/replay_v2.py", "audit/replay_final.json"]
    return {name: sha(BASE / name) for name in paths}


def word(word, q1, q2):
    value = F(0)
    for d, q in ((F(1, 4), q1), (F(1, 8), q2)):
        for sign, mass in ((1, q / 2), (-1, (1 - q) / 2)):
            p = F(1, 2) + sign * d
            value += mass * p**sum(word) * (1 - p)**(len(word) - sum(word))
    return value


def probabilities(q1, q2, policy):
    result = []
    for first, second in product((0, 1), repeat=2):
        if policy == "same_coin" or (policy == "feedback" and first == 1):
            result.append(word((first, second), q1, q2))
        else:
            result.append(word((first,), q1, q2) * word((second,), q1, q2))
    assert sum(result) == 1 and min(result) > 0
    return result


def evaluate(coefficients, x):
    return sum(value * x**i for i, value in enumerate(coefficients))


def interpolate(xs, ys):
    # Exact Vandermonde elimination; independent of the author's polynomial
    # multiplication and differentiation routines.
    n = len(xs)
    rows = [[x**j for j in range(n)] + [y] for x, y in zip(xs, ys)]
    for i in range(n):
        pivot = next(j for j in range(i, n) if rows[j][i])
        rows[i], rows[pivot] = rows[pivot], rows[i]
        scale = rows[i][i]
        rows[i] = [x / scale for x in rows[i]]
        for j in range(n):
            if j != i:
                scale = rows[j][i]
                rows[j] = [x - scale * y for x, y in zip(rows[j], rows[i])]
    return [row[-1] for row in rows]


def main():
    before = sources()
    spec = spec_from_file_location("full_class_author_certificate", BASE / "lower/full_class_certificate.py")
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    result = module.certify()
    saved = json.loads((BASE / "lower/full_class_certificate.json").read_text())
    assert result == saved
    rho, prior = F(1, 4), F(1074499095, 2147483648)
    null, hard = probabilities(F(0), F(0), "feedback"), probabilities(F(0), F(1, 2), "feedback")
    outputs = [rho * prior * b / ((1 - prior) * a + prior * b) for a, b in zip(null, hard)]
    literal = [F(26862477375, 237281040413), F(3223497285, 24696819223),
               F(1074499095, 8589934592), F(22564480995, 146053120736)]
    assert outputs == literal == list(map(F, result["adaptive_output_table"]))

    def risk(A, theta):
        q1, q2 = 16 * A - 2 * theta, 4 * theta - 16 * A
        assert q1 >= 0 and q2 >= 0 and q1 + q2 <= F(1, 2)
        return sum(p * (y - theta)**2 for p, y in zip(probabilities(q1, q2, "feedback"), outputs))

    # Independent direct-latent check across the full feasible triangular grid.
    count = 0
    polynomial_cells = [[F(x) for x in cell] for cell in result["adaptive_probability_polynomials_in_A"]]
    max_grid_risk = F(0)
    for i in range(17):
        for j in range(17 - i):
            q1, q2 = F(i, 32), F(j, 32)
            A, theta = q1 / 8 + q2 / 16, (q1 + q2) / 2
            direct = probabilities(q1, q2, "feedback")
            assert direct == [evaluate(cell, A) for cell in polynomial_cells]
            assert probabilities(q1, q2, "same_coin") == [F(61, 128) - 2*A, F(27, 128), F(27, 128), F(13, 128) + 2*A]
            max_grid_risk = max(max_grid_risk, risk(A, theta))
            count += 1
    assert count == 153

    edge_details = []
    for index, (slope, intercept, lo, hi) in enumerate([
        (F(4), F(0), F(0), F(1, 16)),
        (F(8), F(0), F(0), F(1, 32)),
        (F(0), rho, F(1, 32), F(1, 16)),
    ]):
        xs = [lo + (hi - lo) * j / 3 for j in range(4)]
        coefficients = interpolate(xs, [risk(x, slope*x + intercept) for x in xs])
        author = list(map(F, result["edge_certificates"][index]["risk_coefficients_ascending"]))
        assert coefficients == author + [F(0)] * (4 - len(author))
        curvature = [2*coefficients[2] + 6*coefficients[3]*x for x in (lo, hi)]
        lower = (F(30), F(124), F(3, 100))[index]
        assert min(curvature) > lower
        edge_details.append(dict(coefficients=list(map(str, coefficients)),
                                 endpoint_curvature=list(map(str, curvature)), lower=str(lower)))
    vertex = [risk(F(0), F(0)), risk(F(1, 32), rho), risk(F(1, 16), rho)]
    assert max(vertex) == max_grid_risk == F(result["full_class_adaptive_upper"]["fraction"])
    bayes = {}
    for policy in ("same_coin", "two_fresh"):
        p0, p1 = probabilities(F(0), F(0), policy), probabilities(F(0), F(1, 2), policy)
        y = [rho*prior*b/((1-prior)*a+prior*b) for a, b in zip(p0, p1)]
        value = (1-prior)*sum(p*z*z for p,z in zip(p0,y)) + prior*sum(p*(z-rho)**2 for p,z in zip(p1,y))
        assert value == F(result["fixed_schedule_bayes_lower"][policy]["fraction"])
        bayes[policy] = value
    assert max(vertex) < F(15443, 1000000) < F(15475, 1000000) < min(bayes.values())

    # Old checked sources retain their original checkpoint evidence. This is
    # a hash-freshness check, not a claim to have rerun their arithmetic here.
    prior_replay = json.loads((HERE / "replay_final.json").read_text())
    prior_freshness = {}
    for path, recorded in prior_replay["source_sha256_after"].items():
        current = sha(BASE / path)
        assert current == recorded
        prior_freshness[path] = current
    after = sources()
    assert before == after
    report = dict(status="PASS: independent full-class rational replay and reviewed-source closure v2",
        utc=datetime.now(timezone.utc).isoformat(), python=platform.python_version(),
        head=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        arithmetic="fractions.Fraction; no seeds or floating-point certification",
        source_sha256_before=before, source_sha256_after=after,
        prior_checkpoint_sources_unchanged=prior_freshness,
        direct_latent_triangular_grid_points=count,
        exact_interpolated_edges=edge_details, vertex_risks=list(map(str, vertex)),
        exact_bayes_lower={name: str(value) for name, value in bayes.items()},
        certificate_simple_bounds=["15443/1000000", "15475/1000000"],
        limits=["Continuum maximum uses the independently reviewed polynomial-convexity proof",
                "Finite approximation theorem is reviewed on paper, not established by this arithmetic",
                "No finite convex program was solved; no unrestricted minimax rate certified"])
    target = HERE / (sys.argv[1] if len(sys.argv) == 2 else "replay_v2.json")
    if target.parent.resolve() != HERE.resolve() or target.exists():
        raise RuntimeError("Output must be a new file in the audit directory")
    target.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("PASS: full-Qrho certificate; 153 direct latent grid checks; 3 exact edge reconstructions; v1 hashes unchanged")


if __name__ == "__main__":
    main()
