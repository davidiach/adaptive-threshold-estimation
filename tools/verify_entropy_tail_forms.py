"""Audit the selection and three-piece forms of the entropy-tail functional.

Theorem 13.2 of the v6 paper states the entropy-tail law with universal
constants 0 < c < C and says the functional has the equivalent selection and
three-piece forms (61)-(62) and that hard measurable assignments suffice;
Lemma 13.1 gives a hard minimizer on finite atomic laws. The library stated the
law in form (61) only and with existential constants not ordered. This group
states the fixed-core split, (61) = (62) before and after the cap, the law with
0 < c < C in both forms, hard measurable partitions in form (62), and a hard
minimizer on finite laws.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the seven targets and three components with their types written out;
4. reports the transitive axioms of every public declaration in the directory.

With --replay the registered modules also go through the toolchain's
independent kernel checker. The statements were written after the proofs;
they are pinned from this audit onward.
"""

from __future__ import annotations

import argparse
import re
import subprocess

from verify_blind_upper_components import FORBIDDEN, LEAN, sha, strip_comments, validate_reports
from verify_sharp_rms import public_names

GROUP = "EntropyTailForms"
NAMES = ("Specification", "Pieces", "Hard", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "4cd767b9bcdd3ac6885fdfa0fd5c85dec3021c31acf09cd30401e97d95cdb25d"
TARGETS = {
    "EntropyTailForms.fixed_core_split": "EntropyTailForms.FixedCoreSplitStatement",
    "EntropyTailForms.three_piece_inf": "EntropyTailForms.ThreePieceInfStatement",
    "EntropyTailForms.three_piece_form": "EntropyTailForms.ThreePieceFormStatement",
    "EntropyTailForms.ordered_law": "EntropyTailForms.OrderedLawStatement",
    "EntropyTailForms.three_piece_law": "EntropyTailForms.ThreePieceLawStatement",
    "EntropyTailForms.hard_three_piece": "EntropyTailForms.HardThreePieceStatement",
    "EntropyTailForms.finite_hard_three_piece": "EntropyTailForms.FiniteHardThreePieceStatement",
}
COMPONENTS = (
    "EntropyTailForms.tailCost_add_le",
    "EntropyTailForms.selectionObjective_le_threePiece",
    "EntropyTailForms.partition_restrict_sum",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (ν : Measure Gap) (h : ℝ), 0 ≤ h →
    (⨅ (τ : Measure Gap) (ζ : Measure Gap) (_ : τ + ζ = ν),
      ζ Set.univ + ENNReal.ofReal h * inverseMass τ) = tailCost ν h :=
  EntropyTailForms.fixed_core_split

example :
  ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (ρ B : ℝ),
    (⨅ (σ : Measure Gap) (_ : σ ≤ μ), selectionObjective μ ρ B σ) =
      ⨅ (σ : Measure Gap) (τ : Measure Gap) (ζ : Measure Gap) (_ : σ + τ + ζ = μ),
        threePieceObjective ρ B σ τ ζ :=
  EntropyTailForms.three_piece_inf

example :
  ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (ρ B : ℝ),
    selection μ ρ B = threePieceSelection μ ρ B :=
  EntropyTailForms.three_piece_form

example :
  ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      ENNReal.ofReal c * selection μ ρ B ≤ rareMinimaxRisk μ ρ B ∧
      rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal C * selection μ ρ B :=
  EntropyTailForms.ordered_law

example :
  ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      ENNReal.ofReal c * threePieceSelection μ ρ B ≤ rareMinimaxRisk μ ρ B ∧
      rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal C * threePieceSelection μ ρ B :=
  EntropyTailForms.three_piece_law

example :
  ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    (⨅ (σ : Measure Gap) (τ : Measure Gap) (ζ : Measure Gap) (_ : σ + τ + ζ = μ),
        threePieceObjective ρ B σ τ ζ) =
      ⨅ (S : Set Gap) (T : Set Gap) (Z : Set Gap)
        (_ : MeasurableSet S ∧ MeasurableSet T ∧ MeasurableSet Z ∧
          Disjoint S T ∧ Disjoint S Z ∧ Disjoint T Z ∧ S ∪ T ∪ Z = Set.univ),
        threePieceObjective ρ B (μ.restrict S) (μ.restrict T) (μ.restrict Z) :=
  EntropyTailForms.hard_three_piece

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], μ.support.Finite →
    ∀ {ρ B : ℝ}, 0 < ρ → ρ ≤ 1/4 → 0 < B →
      ∃ S T Z : Set Gap, MeasurableSet S ∧ MeasurableSet T ∧ MeasurableSet Z ∧
        Disjoint S T ∧ Disjoint S Z ∧ Disjoint T Z ∧ S ∪ T ∪ Z = Set.univ ∧
        μ.restrict S + μ.restrict T + μ.restrict Z = μ ∧
        (∀ σ τ ζ : Measure Gap, σ + τ + ζ = μ →
          threePieceObjective ρ B (μ.restrict S) (μ.restrict T) (μ.restrict Z) ≤
            threePieceObjective ρ B σ τ ζ) ∧
        threePieceSelection μ ρ B = min (ENNReal.ofReal ρ)
          (threePieceObjective ρ B (μ.restrict S) (μ.restrict T) (μ.restrict Z)) :=
  EntropyTailForms.finite_hard_three_piece

example : ∀ (τ ζ : Measure Gap) {h : ℝ}, 0 ≤ h →
    tailCost (τ + ζ) h ≤ ζ Set.univ + ENNReal.ofReal h * inverseMass τ :=
  @EntropyTailForms.tailCost_add_le

example : ∀ {μ σ τ ζ : Measure Gap} [IsFiniteMeasure μ], σ + τ + ζ = μ → ∀ (ρ B : ℝ),
    selectionObjective μ ρ B σ ≤ threePieceObjective ρ B σ τ ζ :=
  @EntropyTailForms.selectionObjective_le_threePiece

example : ∀ (μ : Measure Gap) {S T Z : Set Gap}, MeasurableSet T → MeasurableSet Z →
    Disjoint S T → Disjoint S Z → Disjoint T Z → S ∪ T ∪ Z = Set.univ →
    μ.restrict S + μ.restrict T + μ.restrict Z = μ :=
  @EntropyTailForms.partition_restrict_sum
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
        raise ValueError("Duplicate entropy-tail forms declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing entropy-tail forms target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed entropy-tail forms specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTail ThresholdHC.EntropyTailForms",
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
    print(f"All {len(TARGETS)} entropy-tail forms targets are certified")


if __name__ == "__main__":
    main()
