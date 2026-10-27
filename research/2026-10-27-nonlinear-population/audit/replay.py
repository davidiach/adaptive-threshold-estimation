"""Independent exact arithmetic replay; writes only in this audit directory.

Finite calculations do not replace the paper proofs or establish the
unrestricted population minimax rate. All reviewed source hashes are pinned.
"""
from datetime import datetime, timezone
from fractions import Fraction as F
from importlib.util import spec_from_file_location, module_from_spec
from itertools import product
from pathlib import Path
import hashlib
import json
import platform
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BASE = HERE.parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path, name):
    spec = spec_from_file_location(name, path)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def hashes():
    names = ["upper/proof.tex", "upper/check_exact.py", "lower/feedback.tex",
             "lower/feedback_certificate.py", "lower/local_information.tex",
             "audit/CLIPPING_BOUNDARY.tex", "audit/LV_AND_PILOT.md",
             "audit/replay.py"]
    return {name: sha(BASE / name) for name in names}


def information(m, v):
    ph, pt = F(1, 2) - m, F(1, 2) + m
    h, c, z = F(1, 4) - m + v, F(1, 4) - v, F(1, 4) + m + v
    j = 4 * m**2 / (ph * pt)
    jh, jt = 4 * m**2 * c / (ph**2 * h), 4 * m**2 * c / (pt**2 * z)
    assert c * pt - ph * h == m - m**2 - v
    assert pt * z - c * ph == m + m**2 + v
    assert jt < j < jh
    ia, io, inn = j + ph * jh + pt * j, j + ph * jh + pt * jt, 2 * j
    assert ia > max(io, inn)
    return dict(zip(("J", "J_H", "J_T", "I_A", "I_O", "I_N"),
                    map(str, (j, jh, jt, ia, io, inn))))


def clip_check():
    # Rational asymmetric two-point mean-zero errors at endpoint/interior
    # targets. This is a finite diagnostic, not a proof of the general lemma.
    records = []
    rho = F(1, 4)
    for theta in (F(0), rho / 4, rho / 2, rho):
        for p in (F(1, 100), F(1, 4), F(1, 2), F(9, 10)):
            for positive in (F(1, 1000), F(1, 2), F(100)):
                negative = -p * positive / (1 - p)
                v = p * positive**2 + (1 - p) * negative**2
                fourth = p * positive**4 + (1 - p) * negative**4
                k = fourth / v**2
                clipped_mse = sum(prob * (min(rho, max(F(0), theta + error)) - theta)**2
                                  for prob, error in ((p, positive), (1-p, negative)))
                lower = min(v, rho**2) / (256 * k**2)
                assert k >= 1 and clipped_mse >= lower
                records.append(dict(theta=str(theta), p=str(p), positive=str(positive),
                    variance=str(v), kurtosis=str(k), clipped_mse=str(clipped_mse),
                    claimed_lower=str(lower)))
    # Standalone seed-noise diagnostic at a fixed target: no estimator
    # implementability claim is made by taking F0 equal to that target here.
    noise = []
    for epsilon in (F(1, 10), F(1, 100), F(1, 1000)):
        theta = rho / 2
        magnitude = 1 / epsilon
        raw = epsilon * magnitude**2
        clipped = epsilon * rho**2 / 4
        assert raw == 1 / epsilon and clipped <= epsilon * rho**2
        noise.append(dict(epsilon=str(epsilon), variance=str(raw), clipped_mse=str(clipped)))
    return dict(kurtosis_finite_checks=records, rare_noise_diagnostic=noise)


def main():
    before = hashes()
    upper = load(BASE / "upper/check_exact.py", "independent_upper_replay")
    lower = load(BASE / "lower/feedback_certificate.py", "independent_lower_replay")
    polynomials = [upper.verify_polynomial(k) for k in range(1, 17)]
    words = 0
    for length in range(5):
        total = F(0)
        for word in product((0, 1), repeat=length):
            p = upper.word_probability(word, 1)
            assert p == upper.word_probability(word, -1)
            total += p
            words += 1
        assert total == 1
    info = information(F(1, 6), F(1, 32))
    assert info == dict(J="1/2", J_H="21/11", J_T="21/172",
                       I_A="97/66", I_O="576/473", I_N="1")
    result = dict(status="PASS: exact finite arithmetic, independently executed",
        utc=datetime.now(timezone.utc).isoformat(), python=platform.python_version(),
        head=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        arithmetic="fractions.Fraction; no floating point or random seeds",
        limits="No Lean formalization; no unrestricted minimax or asymptotic certificate",
        source_sha256_before=before,
        upper_polynomial_checks=polynomials, upper_local_words=words,
        upper_feedback=upper.feedback_check(), upper_depth_tail=upper.depth_tail_check(),
        lower_feedback_cases=[lower.certify(*case) for case in lower.CASES],
        quadratic_information=info,
        clipping=clip_check(), source_sha256_after=hashes())
    assert result["source_sha256_before"] == result["source_sha256_after"]
    target = HERE / (sys.argv[1] if len(sys.argv) == 2 else "replay.json")
    if target.parent.resolve() != HERE.resolve() or target.exists():
        raise RuntimeError("Output must be a new file in this audit directory")
    target.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("PASS: 16 polynomial checks; 31 words; 2048 feedback transcripts; 3 feedback certificates; FI identities; 48 clipping checks")


if __name__ == "__main__":
    main()
