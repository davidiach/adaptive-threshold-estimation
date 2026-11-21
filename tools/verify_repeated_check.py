"""Audit the repeated-check counterexample of the confidence-transfer package.

The note ANYTIME.md of research/2026-10-30-confidence-transfer shows that
repeatedly inspecting a fixed-time interval is not valid: for iid coins with
success probability theta <= 1/4, the interval H_n/n +- sqrt(3/(4n)) misses
theta with probability at most 1/4 at every fixed n (display (28)), while at
theta = 1/4 the check (4 H_n - n)^2 > 12 n fires at some n <= 512 with
probability 0.42809100970105... (display (29)). The group checks (28) by
Chebyshev with the exact variance, (29) as a 16-digit bracket from the exact
value 1 - S/4^512 with an integer survivor weight S computed by a
decide +kernel certificate, and the first-crossing stopping rule. The note's
displayed 17 digits are a floating-point rendering; the exact value is
slightly below them.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the three targets and three components with their types written out;
4. reports the transitive axioms of every public declaration in the directory.

With --replay the registered modules also go through the toolchain's
independent kernel checker, which re-evaluates the survivor certificate.
The statements were written after the proofs; they are pinned from this
audit onward.
"""

from __future__ import annotations

import argparse
import re
import subprocess

from verify_blind_upper_components import FORBIDDEN, LEAN, sha, strip_comments, validate_reports
from verify_sharp_rms import public_names

GROUP = "RepeatedCheck"
NAMES = ("Specification", "FixedTime", "Row", "Certificate", "PathCount", "Exact", "StopRule", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "f35ec78ae66f38239f91e4d4c79a9f80f973c5e01f75000ce8f133ccfbf75996"
TARGETS = {
    "RepeatedCheck.fixed_time": "RepeatedCheck.FixedTimeStatement",
    "RepeatedCheck.repeated_check": "RepeatedCheck.RepeatedCheckStatement",
    "RepeatedCheck.repeated_check_invalid": "RepeatedCheck.RepeatedCheckInvalidStatement",
}
COMPONENTS = (
    "RepeatedCheck.repeated_check_exact",
    "RepeatedCheck.stopped_check",
    "RepeatedCheck.stopTime_observable",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ θ : unitInterval, (θ : ℝ) ≤ 1/4 → ∀ n : ℕ,
    (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false θ)).real
      {ω | 3 * (n : ℝ) < 4 * ((((Finset.range n).filter (fun t => ω t = true)).card : ℝ) - n * (θ : ℝ)) ^ 2} ≤ 1/4 :=
  RepeatedCheck.fixed_time

example :
  ∀ θ : unitInterval, (θ : ℝ) = 1/4 →
    4280910097010513 / 10^16 < (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false θ)).real
        {ω | ∃ n : ℕ, n ≤ 512 ∧ 12 * (n : ℝ) < (4 * (((Finset.range n).filter (fun t => ω t = true)).card : ℝ) - n) ^ 2} ∧
    (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false θ)).real
        {ω | ∃ n : ℕ, n ≤ 512 ∧ 12 * (n : ℝ) < (4 * (((Finset.range n).filter (fun t => ω t = true)).card : ℝ) - n) ^ 2} < 4280910097010514 / 10^16 :=
  RepeatedCheck.repeated_check

example :
  ∀ θ : unitInterval, (θ : ℝ) = 1/4 →
    (∀ n : ℕ, (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false θ)).real
        {ω | 12 * (n : ℝ) < (4 * (((Finset.range n).filter (fun t => ω t = true)).card : ℝ) - n) ^ 2} ≤ 1/4) ∧
    1/4 < (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false θ)).real
        {ω | ∃ n : ℕ, n ≤ 512 ∧ 12 * (n : ℝ) < (4 * (((Finset.range n).filter (fun t => ω t = true)).card : ℝ) - n) ^ 2} :=
  RepeatedCheck.repeated_check_invalid

example : ∀ (θ : unitInterval), (θ : ℝ) = 1/4 →
    (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false θ)).real
        {ω | ∃ n : ℕ, n ≤ 512 ∧
          12 * (n : ℝ) < (4 * (((Finset.range n).filter (fun t => ω t = true)).card : ℝ) - n) ^ 2} =
      1 - (survivorTotal : ℝ) / 4 ^ 512 :=
  RepeatedCheck.repeated_check_exact

example : ∀ (θ : unitInterval), (θ : ℝ) = 1/4 →
    1/4 < (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false θ)).real
        {ω | 12 * (stopTime 512 ω : ℝ) <
          (4 * (headCount (stopTime 512 ω) ω : ℝ) - stopTime 512 ω) ^ 2} :=
  RepeatedCheck.stopped_check

example : ∀ (N n : ℕ) (ω ω' : ℕ → Bool), (∀ t < n, ω t = ω' t) →
    stopTime N ω = n → stopTime N ω' = n :=
  RepeatedCheck.stopTime_observable
"""


def modules() -> list[str]:
    return [f"{GROUP}.{name}" for name in NAMES]


def declared_roots() -> set[str]:
    found = {p.stem for p in SOURCE.glob("*.lean")}
    if found != set(NAMES) or len(NAMES) != len(set(NAMES)):
        raise ValueError(f"Unregistered or missing {GROUP} module")
    roots: list[str] = []
    for name in NAMES:
        source = strip_comments((SOURCE / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in {GROUP}/{name}.lean")
        names_here = public_names(source, f"{GROUP}/{name}.lean")
        if any(not root.startswith(f"ThresholdHC.{GROUP}.") for root in names_here):
            raise ValueError(f"{GROUP}/{name}.lean must declare in ThresholdHC.{GROUP}")
        roots.extend(names_here)
    if len(roots) != len(set(roots)):
        raise ValueError("Duplicate repeated-check declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing repeated-check target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed repeated-check specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.RepeatedCheck",
        *[f"example : {statement} := {theorem}" for theorem, statement in sorted(TARGETS.items())],
        EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    if ("\n" + EXACT).count("\nexample") != EXACT_COUNT:
        raise ValueError("Each target and component needs exactly one restated statement")
    for name in list(TARGETS) + list(COMPONENTS):
        if len(re.findall(rf":=\s*@?{re.escape(name)}\n", EXACT)) != 1:
            raise ValueError("Each target and component needs exactly one restated statement")
    return source, roots


def replay_modules() -> list[str]:
    return ["ThresholdHC." + module for module in modules()]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--replay", action="store_true",
                        help="also replay the registered modules through leanchecker")
    parser.add_argument("--jobs", type=int, default=3, help="parallel kernel replays")
    args = parser.parse_args()
    source, roots = audit_input()
    subprocess.run(["lake", "build", *replay_modules()], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {EXACT_COUNT} exact statements and {len(roots)} transitive axiom reports")
    if args.replay:
        from verify_project_axioms import replay
        replay(replay_modules(), "lake", args.jobs)
        print(f"Replayed {len(modules())} modules through the independent kernel checker")
    print(f"All {len(TARGETS)} repeated-check targets are certified")


if __name__ == "__main__":
    main()
