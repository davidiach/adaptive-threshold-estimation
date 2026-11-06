"""Audit the observable paid-pilot/selected-continuation stage.

This checks execution, freshness, caps and original-experiment output laws.
It does not instantiate the statistical pilot or prove an oracle risk bound.
"""

import subprocess
from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.ArbitraryLawAdaptation.LearnedStage
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget
open ThresholdHC.ObservableSimulation ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.LawAdaptation
variable {R : Type} [MeasurableSpace R]

example : ∀ S : LearnedStage R, S.cap = S.pilotCost + S.continuationCost := fun _ => rfl
example : ∀ (S : LearnedStage R) (xs : List Bool),
    S.learnedLaw xs = envelopeLaw (prefixMinimum (S.upper xs)) S.depth := fun _ _ => rfl
example : ∀ (S : LearnedStage R) (xs : List Bool), IsProbabilityMeasure (S.learnedLaw xs) :=
  @LearnedStage.learnedLaw_probability R _
example : ∀ (S : LearnedStage R) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupport : μ (Set.Iio 0) = 0) (xs : List Bool)
    (hgrid : ∀ j ≤ S.depth, μ.real (Set.Iic (gridPoint j)) ≤ S.upper xs j) (x : ℝ),
    μ (Set.Iic x) ≤ S.learnedLaw xs (Set.Iic x) := @LearnedStage.learnedLaw_dominates R _
example : ∀ (S : LearnedStage R) (r : R), S.reader r =
    thenChoose S.pilotCost (Nat.pair 0 ∘ S.pilot)
      (fun xs => Nat.pair 1 ∘ S.continuation (S.learnedLaw xs) r) := fun _ _ => rfl
example : ∀ (S : LearnedStage R) (r : R) (xs : List Bool),
    S.historyInterval r xs = S.interval (S.learnedLaw (xs.take S.pilotCost)) r
      (xs.drop S.pilotCost) := fun _ _ _ => rfl
example : ∀ (S : LearnedStage R) (r : R) (s : Table), S.tableInterval r s =
    let v := (readBlock S.pilotCost S.pilot (s ∘ Nat.pair 0)).1
    let law := S.learnedLaw v
    S.interval law r (readBlock S.continuationCost (S.continuation law r)
      (s ∘ Nat.pair 1)).1 := fun _ _ _ => rfl
example : ∀ (S : LearnedStage R) (s : Table) (j : ℕ),
    (readBlock S.pilotCost (Nat.pair 0 ∘ S.pilot) s).2 (Nat.pair 1 j) = s (Nat.pair 1 j) :=
  @LearnedStage.pilot_fresh R _
example : ∀ (S : LearnedStage R) (r : R) (s : Table),
    S.historyInterval r (readBlock S.cap (S.reader r) s).1 = S.tableInterval r s :=
  @LearnedStage.interval_readBlock R _
example : ∀ (S : LearnedStage R) (xs : List Bool), Measurable (fun r => S.reader r xs) :=
  @LearnedStage.measurable_reader R _
example : ∀ (S : LearnedStage R) (xs : List Bool), Measurable (fun r => S.historyInterval r xs) :=
  @LearnedStage.measurable_historyInterval R _
example : ∀ (S : LearnedStage R) (upper : Bool),
    (S.endpoint upper).policy = fun r => stopAt S.cap (S.reader r) := fun _ _ => rfl
example : ∀ (S : LearnedStage R) (upper : Bool),
    (S.endpoint upper).output = fun z =>
      let I := S.historyInterval z.1 (processHistory z.2 S.cap)
      if upper then I.2 else I.1 := fun _ _ => rfl
example : ∀ (S : LearnedStage R) (upper : Bool), PathwiseCap (S.endpoint upper) S.cap :=
  @LearnedStage.endpoint_cap R _
example : ∀ S : LearnedStage R, (S.endpoint true).policy = (S.endpoint false).policy :=
  @LearnedStage.endpoint_policy_eq R _
example : ∀ (S : LearnedStage R) (upper : Bool) (r : R) (s : Table),
    (S.endpoint upper).output (r,populationPath ((S.endpoint upper).policy r) s) =
      if upper then (S.tableInterval r s).2 else (S.tableInterval r s).1 :=
  @LearnedStage.endpoint_output R _
example : ∀ (S : LearnedStage R) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (experimentLaw μ (S.endpoint false) q).map
      (fun z => ((S.endpoint false).output (z.1.1,z.2), (S.endpoint true).output (z.1.1,z.2))) =
      (originalSimulationLaw μ (S.endpoint false) q).map
        (fun z => S.tableInterval z.1 z.2) := @LearnedStage.original_interval_law R _
"""
    roots = {"ThresholdHC.ArbitraryLawAdaptation.LearnedStage." + name for name in [
        "cap", "learnedLaw", "learnedLaw_probability", "learnedLaw_dominates",
        "reader", "historyInterval", "tableInterval", "pilot_fresh",
        "interval_readBlock", "measurable_reader", "measurable_historyInterval", "endpoint",
        "endpoint_cap", "endpoint_policy_eq", "endpoint_output", "original_interval_law",
    ]}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.ArbitraryLawAdaptation.LearnedStage"],
                   cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "-j1", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {source.count('example ')} exact statements and {len(roots)} transitive reports")


if __name__ == "__main__":
    main()
