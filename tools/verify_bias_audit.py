"""Audit the bias audit of the constant search.

proposals/constants/BIAS_AUDIT.md shows that the finite-grid winner of the
constant search, threshold coefficients (k1, k2) = (1/4, 1/2), violates the
uniform v4 error envelope min(1, (N d^2)^-2): at d = 1/10, positive sign and
cap N = 2^97 the misclassification probability is at least (2/5)^128, more
than 2907 times the envelope (exact ratio 2^318/5^132). It also shows that
any k1 >= 0, k2 >= 1 keeps the envelope, with the explicit bound
exp(-2x) + (2/3) exp(-2 k1) x^-2 at x = N d^2. The group checks both against
the frozen classifier error errProbK of Statements2.lean, and states that the
grid winner fails the form of the frozen target Targets.lemma6_error.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the three targets and three components with their types written out;
4. reports the transitive axioms of every public declaration in the directory.

With --replay the registered modules also go through the toolchain's
independent kernel checker. The statements were written before the proofs
and reviewed before the pin; they are pinned from this audit onward.
"""

from __future__ import annotations

import argparse
import re
import subprocess

from verify_blind_upper_components import FORBIDDEN, LEAN, sha, strip_comments, validate_reports
from verify_sharp_rms import public_names

GROUP = "BiasAudit"
NAMES = ("Specification", "Measure", "Counterexample", "SmallerThreshold", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "3cbec57449964fbdac1dd6ecd9c69ad7c0483cbf65f80dc5838e141be390a2cd"
TARGETS = {
    "BiasAudit.grid_winner_counterexample": "BiasAudit.GridWinnerCounterexampleStatement",
    "BiasAudit.grid_winner_fails_envelope": "BiasAudit.GridWinnerFailsEnvelopeStatement",
    "BiasAudit.smaller_threshold_error": "BiasAudit.SmallerThresholdErrorStatement",
}
COMPONENTS = (
    "BiasAudit.errProbK_eq_measure_gen",
    "BiasAudit.errorUnionBoundK_le",
    "BiasAudit.explicit_le_envelope",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  (2/5 : ℝ) ^ 128 ≤ errProbK (1/4) (1/2) 97 (1/10) true ∧
    2907 * min 1 ((((2 : ℝ) ^ 97 * (1/10) ^ 2)⁻¹) ^ 2) < (2/5 : ℝ) ^ 128 :=
  BiasAudit.grid_winner_counterexample

example :
  ¬ ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    errProbK (1/4) (1/2) L d S ≤ min 1 ((((2 : ℝ) ^ L * d ^ 2)⁻¹) ^ 2) :=
  BiasAudit.grid_winner_fails_envelope

example :
  ∀ (k₁ k₂ : ℝ), 0 ≤ k₁ → 1 ≤ k₂ → ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    errProbK k₁ k₂ L d S ≤
        Real.exp (-2 * ((2 : ℝ) ^ L * d ^ 2)) +
          2/3 * Real.exp (-2 * k₁) * (((2 : ℝ) ^ L * d ^ 2)⁻¹) ^ 2 ∧
      errProbK k₁ k₂ L d S ≤ min 1 ((((2 : ℝ) ^ L * d ^ 2)⁻¹) ^ 2) :=
  BiasAudit.smaller_threshold_error

example : ∀ (k1 k2 : ℝ) (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2),
    errProbK k1 k2 L d S = (tapeMeasure (coinParameter d S hd hdmax)).real
      {ω | firstDecision (finiteBoundary k1 k2) (fun j => dyadicMean observations j ω) L ≠
        bit S} :=
  BiasAudit.errProbK_eq_measure_gen

example : ∀ {k1 k2 : ℝ}, 0 ≤ k1 → 1 ≤ k2 → ∀ (L : ℕ) {d : ℝ}, 0 < d →
    BiasAudit.errorUnionBoundK k1 k2 L d ≤
      Real.exp (-2 * (cap L * d ^ 2)) + 2/3 * Real.exp (-2 * k1) * ((cap L * d ^ 2)⁻¹) ^ 2 :=
  @BiasAudit.errorUnionBoundK_le

example : ∀ {k1 : ℝ}, 0 ≤ k1 → ∀ {x : ℝ}, 0 < x →
    Real.exp (-2 * x) + 2/3 * Real.exp (-2 * k1) * (x⁻¹) ^ 2 ≤ (x⁻¹) ^ 2 :=
  @BiasAudit.explicit_le_envelope
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
        raise ValueError("Duplicate bias-audit declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing bias-audit target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed bias-audit specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Uniform713 ThresholdHC.BiasAudit",
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
    print(f"All {len(TARGETS)} bias-audit targets are certified")


if __name__ == "__main__":
    main()
