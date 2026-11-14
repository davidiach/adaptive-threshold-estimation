"""Audit the planner's output as a named estimator.

Every definition and theorem of the module is restated in full, so a changed
definition, hypothesis or constant is an elaboration error, and the
transitive axioms of every declaration are reported. A declaration of the
module that the registry cannot read, or that is not registered here, is an
error. Prints the kernel report; writes nothing.
"""

import subprocess
from verify_blind_upper_components import (FORBIDDEN, LEAN, bind_restatements,
                                           registered_names, strip_comments,
                                           validate_reports)

MODULE = "ThresholdHC.KnownLawPlanner.PlannerEstimator"
SOURCE = LEAN / "ThresholdHC/KnownLawPlanner/PlannerEstimator.lean"
NAMES = [
    "core_support_of_eq", "exists_bandEdge_lt", "quantilePlanEstimator", "RunsPlan",
    "planner_output_of_rates", "exactWeights", "exact_planner_output", "tight_planner_output",
]
SPLIT = ("[IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]")
QUANTILE = ("(hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ) "
            "(hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) "
            "(hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)")


def declared_names():
    """Every declaration of the module, after rejecting proof escapes."""
    source = strip_comments(SOURCE.read_text(encoding="utf-8"))
    if FORBIDDEN.search(source):
        raise ValueError("Forbidden proof escape in " + SOURCE.name)
    return registered_names(source)


def audit_input():
    if sorted(declared_names()) != sorted(NAMES):
        raise ValueError("Unregistered or missing planner-estimator declaration")
    plan = ("planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) "
            "(planTerminal hρ B E.unresolved)) w")
    exact_plan = ("quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN (SplitEnclosure.exact σ τ ζ N) "
                  "(eta_vanishes (σ+τ)) B (exactWeights σ τ ζ hρ B N)")
    exact_runs = ("RunsPlan (SplitEnclosure.exact σ τ ζ N) hρ (eta_vanishes (σ+τ)) B "
                  "(exactWeights σ τ ζ hρ B N)")
    tight_plan = "quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN E hE.vanishes B w"
    tight_c = "ENNReal.ofReal (1 + 8/5 * max 4096 (224000 * sqrt θ))"
    K = "ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B"
    weights = ("sqrt (17*levelAccuracy ρ i.val / planCost E ρ "
               "(searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved) i)")
    source = f"""
import ThresholdHC.KnownLawPlanner.PlannerEstimator
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Set Real
open scoped NNReal ENNReal BigOperators
open ThresholdHC.KnownLawPlanner
open ThresholdHC.Tier6 (Gap AdaptiveEstimator)
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailUpper
open ThresholdHC.EntropyTailAssembly ThresholdHC.EntropyTailExecution
open ThresholdHC.RareAboveTwo ThresholdHC.ArbitraryLawAdaptation

example : ∀ (σ τ ζ : Measure Gap) {{ρ : ℝ}} (hcore : σ = quantileCore (σ+τ+ζ) ρ),
    ∀ᵐ d : Gap ∂σ, quantileThreshold (σ+τ+ζ) ρ ≤ (d:ℝ) := @core_support_of_eq
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {{ρ : ℝ}} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1),
    ∃ N : ℕ, bandEdge N < quantileThreshold μ ρ := @exists_bandEdge_lt
example : ∀ (σ τ ζ : Measure Gap) {SPLIT} {{ρ : ℝ}} {{N : ℕ}} (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1/4) (hcore : σ = quantileCore (σ+τ+ζ) ρ)
    (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ) (E : SplitEnclosure σ τ ζ N)
    (hvan : EnvelopeVanishes E.resolvedError) (B : ℝ)
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ)
    (ht : 0 < quantileThreshold (σ+τ+ζ) ρ)
    (hs : ∀ᵐ d : Gap ∂σ, quantileThreshold (σ+τ+ζ) ρ ≤ (d:ℝ)),
    quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN E hvan B w =
      planEstimator σ τ ζ ht hs hN hρ hρ4 (searchCaps E.resolvedError hvan hρ) ({plan}) :=
  by intros; rfl
example : ∀ {{σ τ ζ : Measure Gap}} {{N : ℕ}} (E : SplitEnclosure σ τ ζ N) {{ρ : ℝ}}
    (hρ : 0 < ρ) (hvan : EnvelopeVanishes E.resolvedError) (B : ℝ)
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ),
    RunsPlan E hρ hvan B w ↔
      2048 * E.unresolved ≤ ρ ∧ sqrt (planCertificate ρ ({plan})) ≤ ρ/2 :=
  by intros; exact Iff.rfl
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] {{ρ : ℝ}}
    (hρ : 0 < ρ) (B : ℝ) (N : ℕ) (i : Fin (planTerminal hρ B (ζ.real univ) + 1)),
    exactWeights σ τ ζ hρ B N i =
      sqrt (17*levelAccuracy ρ i.val /
        planCost (SplitEnclosure.exact σ τ ζ N) ρ
          (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ) (planTerminal hρ B (ζ.real univ)) i) :=
  by intros; rfl
example : ∀ (σ τ ζ : Measure Gap) {SPLIT} {{ρ B C : ℝ}} {{N : ℕ}} (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hcore : σ = quantileCore (σ+τ+ζ) ρ)
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ))
    (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ) (E : SplitEnclosure σ τ ζ N)
    (hvan : EnvelopeVanishes E.resolvedError)
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ)
    (hw : 2048 * E.unresolved ≤ ρ → ∀ i, 0 < w i)
    (hplan : 2048 * E.unresolved ≤ ρ →
      ENNReal.ofReal (min (ρ/2) (sqrt (planCertificate ρ ({plan})))) ≤
        ENNReal.ofReal C * {K})
    (hfall : ρ < 2048 * E.unresolved → ENNReal.ofReal (ρ/2) ≤ ENNReal.ofReal C * {K}),
    (RunsPlan E hρ hvan B w →
      RareBudget (σ+τ+ζ) (quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN E hvan B w) ρ B ∧
      rareRisk (σ+τ+ζ) (quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN E hvan B w) ρ ≤
        ENNReal.ofReal C * {K}) ∧
    (¬ RunsPlan E hρ hvan B w →
      RareBudget (σ+τ+ζ) (constantEstimator (ρ/2)) ρ B ∧
      rareRisk (σ+τ+ζ) (constantEstimator (ρ/2)) ρ ≤ ENNReal.ofReal C * {K}) :=
  @planner_output_of_rates
example : ∀ (σ τ ζ : Measure Gap) {SPLIT} {{ρ B : ℝ}} {{N : ℕ}} (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1/4) (hB : 0 < B) {QUANTILE}
    (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ),
    ({exact_runs} →
      RareBudget (σ+τ+ζ) ({exact_plan}) ρ B ∧
      rareRisk (σ+τ+ζ) ({exact_plan}) ρ ≤ ENNReal.ofReal 44801 * {K}) ∧
    (¬ {exact_runs} →
      RareBudget (σ+τ+ζ) (constantEstimator (ρ/2)) ρ B ∧
      rareRisk (σ+τ+ζ) (constantEstimator (ρ/2)) ρ ≤ ENNReal.ofReal 44801 * {K}) :=
  @exact_planner_output
example : ∀ (σ τ ζ : Measure Gap) {SPLIT} {{ρ B θ : ℝ}} {{N : ℕ}} (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hθ : 0 ≤ θ) {QUANTILE}
    (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ)
    (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (ζ.real univ))
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ)
    (hlow : ∀ i, {weights} ≤ w i)
    (hup : ∀ i, w i ≤ θ * {weights}),
    (RunsPlan E hρ hE.vanishes B w →
      RareBudget (σ+τ+ζ) ({tight_plan}) ρ B ∧
      rareRisk (σ+τ+ζ) ({tight_plan}) ρ ≤ {tight_c} * {K}) ∧
    (¬ RunsPlan E hρ hE.vanishes B w →
      RareBudget (σ+τ+ζ) (constantEstimator (ρ/2)) ρ B ∧
      rareRisk (σ+τ+ζ) (constantEstimator (ρ/2)) ρ ≤ {tight_c} * {K}) :=
  @tight_planner_output
"""
    bind_restatements(source, NAMES)
    roots = {"ThresholdHC.KnownLawPlanner." + name for name in NAMES}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", MODULE], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "-j1", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {source.count('example ')} exact statements and {len(roots)} transitive reports")


if __name__ == "__main__":
    main()
