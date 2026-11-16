"""Audit the CDF-to-continuation bridge, including its exact quantifier order.

Every declaration is independently restated and checked for allowed transitive
axioms. Unreadable, missing, or unregistered declarations fail closed. Prints
the report without changing published evidence.
"""

import subprocess

from verify_blind_upper_components import (
    FORBIDDEN, LEAN, bind_restatements, registered_names, strip_comments, validate_reports,
)

MODULE = "ThresholdHC.RobustContinuation.CDFBridge"
SOURCES = [LEAN / "ThresholdHC/RobustContinuation/CDFBridge.lean"]
NAMES = [
    "mappedGap_support", "mappedGap_below_zero", "mappedGap_cdf_top",
    "zeroAtomLaw_probability", "zeroAtomLaw_below_zero", "zeroAtomLaw_cdf_top",
    "exists_robust_coupling_of_cdf", "coupling_sign_mass", "coupling_sign_budget",
    "cdf_robust_enclosed_plan_valid", "cdf_robust_searched_plan_valid", "cdf_robust_planner_rate",
]


def declared_names():
    found = []
    for path in SOURCES:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + path.name)
        found += registered_names(source)
    return found


def audit_input():
    if sorted(declared_names()) != sorted(NAMES):
        raise ValueError("Unregistered or missing robust-CDF declaration")
    source = """
import ThresholdHC.RobustContinuation.CDFBridge
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open ThresholdHC.RobustContinuation
open ThresholdHC.Tier6 (Gap SignLaw AdaptiveEstimator signMean)
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.RareAboveTwo
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailAssembly ThresholdHC.KnownLawPlanner

example : ∀ (μ : Measure Gap),
    ∀ᵐ d : ℝ ∂μ.map Subtype.val, d ∈ Ioc 0 (1/2) := @mappedGap_support
example : ∀ (μ : Measure Gap),
    μ.map Subtype.val (Iio 0) = 0 := @mappedGap_below_zero
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    cdf (μ.map Subtype.val) (1/2) = 1 := @mappedGap_cdf_top
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] {z₀ : ℝ}
    (hz0 : 0 ≤ z₀) (hz1 : z₀ ≤ 1),
    IsProbabilityMeasure (zeroAtomLaw z₀ η) := @zeroAtomLaw_probability
example : ∀ (η : Measure Gap) (z₀ : ℝ),
    zeroAtomLaw z₀ η (Iio 0) = 0 := @zeroAtomLaw_below_zero
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] {z₀ : ℝ}
    (hz0 : 0 ≤ z₀) (hz1 : z₀ ≤ 1),
    cdf (zeroAtomLaw z₀ η) (1/2) = 1 := @zeroAtomLaw_cdf_top
example : ∀ (η μ : Measure Gap) [IsProbabilityMeasure η] [IsProbabilityMeasure μ]
    {z₀ : ℝ} (hz0 : 0 ≤ z₀) (hz1 : z₀ ≤ 1)
    (hdom : ∀ x, cdf (μ.map Subtype.val) x ≤ cdf (zeroAtomLaw z₀ η) x),
    ∃ (π : Measure (Gap × Gap)) (μ₀ : Measure Gap),
      IsFiniteMeasure π ∧ IsFiniteMeasure μ₀ ∧
      (∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) ∧
      π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η ∧
      μ = π.map Prod.snd + μ₀ ∧ μ₀.real univ = z₀ := @exists_robust_coupling_of_cdf
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (μ₀ μ : Measure Gap)
    [IsFiniteMeasure μ₀] (hμ : μ = π.map Prod.snd + μ₀) (q : SignLaw),
    (∫ z, q.val z.2 ∂π) + (∫ d, q.val d ∂μ₀) = signMean μ q.val := @coupling_sign_mass
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (μ₀ μ : Measure Gap)
    [IsFiniteMeasure μ₀] [IsFiniteMeasure μ] (hμ : μ = π.map Prod.snd + μ₀)
    (q : SignLaw) {ρ : ℝ} (hq : RarePrior μ ρ q),
    (∫ z, q.val z.2 ∂π) ≤ ρ := @coupling_sign_budget
example : ∀ (η μ : Measure Gap) [IsProbabilityMeasure η] [IsProbabilityMeasure μ]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {z₀ : ℝ} (hz0 : 0 ≤ z₀) (hc : 0 < 1 - z₀)
    (hdesign : σ+τ+ζ = ENNReal.ofReal (1 - z₀) • η)
    (hdom : ∀ x, cdf (μ.map Subtype.val) x ≤ cdf (zeroAtomLaw z₀ η) x)
    {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hρc : ρ ≤ 1 - z₀) (E : SplitEnclosure σ τ ζ N)
    (hE₀ : ζ.real univ + z₀ ≤ E.unresolved) (κ : ℕ → ℕ) {J : ℕ}
    (hκ : ∀ l, l ≤ J → E.resolvedError (4 ^ κ l) ≤ levelAccuracy ρ l/8)
    (hzJ : E.unresolved ≤ levelAccuracy ρ J/8)
    (r : Fin (J+1) → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ))
    (hwork : ∑ i : Fin (J+1), (r i:ℝ) * adjacentCost (fun l => E.price ρ l (κ l)) i.val ≤ B),
    RareBudget μ (robustPlanEstimator η σ ht hs hN hc hρc κ r) ρ B ∧
      rareRisk μ (robustPlanEstimator η σ ht hs hN hc hρc κ r) ρ ≤
        ENNReal.ofReal (Real.sqrt (planCertificate ρ r)) := @cdf_robust_enclosed_plan_valid
example : ∀ (η μ : Measure Gap) [IsProbabilityMeasure η] [IsProbabilityMeasure μ]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {z₀ : ℝ} (hz0 : 0 ≤ z₀) (hc : 0 < 1 - z₀)
    (hdesign : σ+τ+ζ = ENNReal.ofReal (1 - z₀) • η)
    (hdom : ∀ x, cdf (μ.map Subtype.val) x ≤ cdf (zeroAtomLaw z₀ η) x)
    {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hρc : ρ ≤ 1 - z₀) (hB : 0 < B) (E : SplitEnclosure σ τ ζ N)
    (hE₀ : ζ.real univ + z₀ ≤ E.unresolved) (hvan : EnvelopeVanishes E.resolvedError)
    {J : ℕ} (hzJ : E.unresolved ≤ levelAccuracy ρ J/8)
    (w : Fin (J+1) → ℝ) (hw : ∀ i, 0 < w i),
    RareBudget μ (robustPlanEstimator η σ ht hs hN hc hρc
        (searchCaps E.resolvedError hvan hρ)
        (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w)) ρ B ∧
      rareRisk μ (robustPlanEstimator η σ ht hs hN hc hρc
        (searchCaps E.resolvedError hvan hρ)
        (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w)) ρ ≤
        ENNReal.ofReal (Real.sqrt (planCertificate ρ
          (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w))) := @cdf_robust_searched_plan_valid
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] {z₀ ρ B : ℝ}
    (hz0 : 0 ≤ z₀) (hzρ : z₀ < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B),
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        (∀ x, cdf (μ.map Subtype.val) x ≤ cdf (zeroAtomLaw z₀ η) x) →
        RareBudget μ A ρ B ∧ rareRisk μ A ρ ≤
          ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B := @cdf_robust_planner_rate
"""
    if source.count("example ") != len(NAMES):
        raise ValueError("Each robust-CDF declaration needs exactly one restated statement")
    bind_restatements(source, NAMES)
    roots = {"ThresholdHC.RobustContinuation." + name for name in NAMES}
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
