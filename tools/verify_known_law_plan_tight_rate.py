"""Audit the rate of a known-law plan computed from upper bounds.

Every definition and theorem of the three modules is restated in full, so a
changed definition, hypothesis or constant is an elaboration error, and the
transitive axioms of every declaration are reported. A declaration in those
modules that is not registered here is an error. Prints the kernel report;
writes nothing.
"""

import subprocess
from verify_blind_upper_components import (FORBIDDEN, LEAN, bind_restatements,
                                           registered_names, strip_comments,
                                           validate_reports)

MODULE = "ThresholdHC.KnownLawPlanner.PlanZeroAtomRate"
SOURCES = [LEAN / "ThresholdHC/KnownLawPlanner" / (name + ".lean")
           for name in ("PlanTightRate", "PlanTightQuantileRate", "PlanZeroAtomRate")]
NAMES = [
    "ordinaryWorkKernel_mono", "ordinaryCost_mono", "errorCapExponent_succ_le",
    "band_entropy_enclosure", "SplitEnclosure.Tight", "SplitEnclosure.exact_tight",
    "SplitEnclosure.Tight.vanishes", "tight_caps_le", "tight_price_le", "SplitEnclosure.price_pos",
    "tight_plan_spread", "plan_rms_of_spread", "tight_plan_rms_le", "tight_planTerminal",
    "rate_arithmetic", "fallback_arithmetic", "tight_plan_rate_real", "tight_quantile_plan_rate",
    "tight_quantile_fallback_rate", "tight_quantile_plan_radius", "tailModulus_smul",
    "scaled_measureCostEntropy", "zero_selection_floor", "zero_split_value",
    "zero_split_comparison", "zero_atom_plan_rate", "zero_atom_fallback_rate",
    "plannedCoefficient", "plannedCoefficient_mono", "zero_atom_plan_rate_dyadic",
    "zero_atom_plan_radius_dyadic",
]


def declared_names():
    """Every declaration of the three modules, after rejecting proof escapes."""
    found = []
    for path in SOURCES:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + path.name)
        found += registered_names(source)
    return found


def audit_input():
    if sorted(declared_names()) != sorted(NAMES):
        raise ValueError("Unregistered or missing tight-rate declaration")
    source = """
import ThresholdHC.KnownLawPlanner.PlanZeroAtomRate
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Set Real
open scoped NNReal ENNReal BigOperators
open ThresholdHC.KnownLawPlanner
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailUpper
open ThresholdHC.EntropyTailAssembly ThresholdHC.EntropyTailExecution
open ThresholdHC.ArbitraryLawAdaptation

example : ∀ {σ τ ζ : Measure Gap} {N : ℕ} (E : SplitEnclosure σ τ ζ N) (z : ℝ),
    E.Tight z ↔
      (E.entropy ≤ 4 * costEntropy (fun j : Fin N => bandCost σ j.val) ∧
      E.tailInverse ≤ 2 * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) ∧
      z ≤ E.unresolved ∧ E.unresolved ≤ 2 * z ∧
      (∀ k : ℕ, E.resolvedError (4 ^ k) ≤ 2 * eta (σ+τ) (4 ^ k)) ∧
      ∀ k : ℕ, E.tailWork (4 ^ k) ≤ 2 * ordinaryCost τ (4 ^ k)) :=
  fun _ _ => Iff.rfl
example : ∀ (Csum : ℝ), plannedCoefficient Csum = 1 + 4 * max 4096 (8 * sqrt 2 * Csum) :=
  fun _ => rfl
example : ∀ {M P : ℝ} (hM : 0 < M) (hMP : M ≤ P) (d : Gap),
    ordinaryWorkKernel M (d:ℝ) ≤ ordinaryWorkKernel P (d:ℝ) := @ordinaryWorkKernel_mono
example : ∀ (τ : Measure Gap) [IsFiniteMeasure τ] {M P : ℝ} (hM : 0 < M) (hMP : M ≤ P),
    ordinaryCost τ M ≤ ordinaryCost τ P := @ordinaryCost_mono
example : ∀ (ν : Measure Gap) [IsFiniteMeasure ν] {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ),
    errorCapExponent ν (levelAccuracy ρ l) (levelAccuracy_pos hρ l) ≤
      errorCapExponent ν (levelAccuracy ρ (l+1)) (levelAccuracy_pos hρ (l+1)) := @errorCapExponent_succ_le
example : ∀ {N : ℕ} {a b : Fin N → ℝ} (ha : ∀ j, 0 ≤ a j) (hab : ∀ j, a j ≤ b j) (hb : ∀ j, b j ≤ 2 * a j),
    costEntropy a ≤ costEntropy b ∧ costEntropy b ≤ 2 * costEntropy a := @band_entropy_enclosure
example : ∀ (σ τ ζ : Measure Gap) (N : ℕ),
    (SplitEnclosure.exact σ τ ζ N).Tight (ζ.real univ) := @SplitEnclosure.exact_tight
example : ∀ {σ τ ζ : Measure Gap} [IsFiniteMeasure σ] [IsFiniteMeasure τ] {N : ℕ} {E : SplitEnclosure σ τ ζ N} {z : ℝ} (hE : E.Tight z),
    EnvelopeVanishes E.resolvedError := @SplitEnclosure.Tight.vanishes
example : ∀ {σ τ ζ : Measure Gap} [IsFiniteMeasure σ] [IsFiniteMeasure τ] {N : ℕ} {E : SplitEnclosure σ τ ζ N} {z : ℝ} (hE : E.Tight z) {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ),
    searchCaps E.resolvedError hE.vanishes hρ l ≤
      errorCapExponent (σ+τ) (levelAccuracy ρ (l+1)) (levelAccuracy_pos hρ (l+1)) := @tight_caps_le
example : ∀ {σ τ ζ : Measure Gap} [IsFiniteMeasure σ] [IsFiniteMeasure τ] {N : ℕ} {E : SplitEnclosure σ τ ζ N} {z : ℝ} (hE : E.Tight z) {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ),
    E.price ρ l (searchCaps E.resolvedError hE.vanishes hρ l) ≤
      4 * levelWorkCertificate σ τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val)) z hρ
      (l+1) := @tight_price_le
example : ∀ {σ τ ζ : Measure Gap} [IsFiniteMeasure σ] [IsFiniteMeasure τ] {N : ℕ} (E : SplitEnclosure σ τ ζ N) {t ρ : ℝ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hρ : 0 < ρ) (hm : 0 < (σ+τ).real univ) (l k : ℕ),
    0 < E.price ρ l k := @SplitEnclosure.price_pos
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] {t ρ z : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hm : ρ/128 < (σ+τ).real univ) (E : SplitEnclosure σ τ ζ N) (hE : E.Tight z) (J : ℕ) (hzJ : z ≤ levelAccuracy ρ J/128),
    allocationCertificate (fun i : Fin (J+1) => 17*levelAccuracy ρ i.val)
      (planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) J) ≤
      224000*(sqrt (ρ*costEntropy (fun j : Fin N => bandCost σ j.val)) +
      ∫ d : Gap, (d:ℝ)⁻¹ ∂τ) := @tight_plan_spread
example : ∀ {ρ B θ S : ℝ} (hρ : 0 < ρ) (hB : 0 < B) (hθ : 0 ≤ θ) {J : ℕ} {k w : Fin (J+1) → ℝ} (hk : ∀ i, 0 < k i) (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val / k i) ≤ w i) (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val / k i)) (hS : allocationCertificate (fun i : Fin (J+1) => 17*levelAccuracy ρ i.val) k ≤ S),
    sqrt (planCertificate ρ (planRates B k w)) ≤ levelAccuracy ρ J + sqrt θ * S / sqrt B := @plan_rms_of_spread
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] {t ρ B θ z : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hB : 0 < B) (hθ : 0 ≤ θ) (hm : ρ/128 < (σ+τ).real univ) (E : SplitEnclosure σ τ ζ N) (hE : E.Tight z) (J : ℕ) (hzJ : z ≤ levelAccuracy ρ J/128) (w : Fin (J+1) → ℝ) (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) J i) ≤ w i) (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) J i)),
    sqrt (planCertificate ρ (planRates B
      (planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) J) w)) ≤
      levelAccuracy ρ J + sqrt θ * (224000*(sqrt (ρ*costEntropy
      (fun j : Fin N => bandCost σ j.val)) + ∫ d : Gap, (d:ℝ)⁻¹ ∂τ)) / sqrt B := @tight_plan_rms_le
example : ∀ {σ τ ζ : Measure Gap} {N : ℕ} {E : SplitEnclosure σ τ ζ N} {z : ℝ} (hE : E.Tight z) {ρ : ℝ} (hρ : 0 < ρ) (B : ℝ) (hz : 2048*E.unresolved ≤ ρ),
    z ≤ levelAccuracy ρ (planTerminal hρ B E.unresolved)/128 ∧
      levelAccuracy ρ (planTerminal hρ B E.unresolved) < 4096*z + ρ/(1+sqrt B) := @tight_planTerminal
example : ∀ {ρ K F V z s δ c m a : ℝ} (hK : 0 ≤ K) (hF : F ≤ K) (hc : 0 ≤ c) (hm : 1/2 ≤ m) (hz : 0 ≤ z) (hV : 0 ≤ V) (hQ : min ρ (z + V) ≤ c * K) (hδ : δ ≤ m * z + F) (hs : s ≤ δ + a * V),
    min (ρ/2) s ≤ (1 + c * max m a) * K := @rate_arithmetic
example : ∀ {ρ K U z c m : ℝ} (a : ℝ) (hρ : 0 ≤ ρ) (hK : 0 ≤ K) (hc : 0 ≤ c) (hm : 1/2 ≤ m) (hzU : z ≤ U) (hQ : min ρ U ≤ c * K) (hfall : ρ < m * z),
    ρ/2 ≤ (1 + c * max m a) * K := @fallback_arithmetic
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] {t ρ B θ z K c : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hρ : 0 < ρ) (hB : 0 < B) (hθ : 0 ≤ θ) (hm : ρ/128 < (σ+τ).real univ) (E : SplitEnclosure σ τ ζ N) (hE : E.Tight z) (hz : 2048 * E.unresolved ≤ ρ) (hK : 0 ≤ K) (hfloor : ρ/(1+sqrt B) ≤ K) (hc : 0 ≤ c) (hQ : min ρ (z + (budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) + budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal))) ≤ c * K) (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ) (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved) i) ≤ w i) (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved) i)),
    min (ρ/2) (sqrt (planCertificate ρ (planRates B
      (planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
      (planTerminal hρ B E.unresolved)) w))) ≤
      (1 + c * max 4096 (224000 * sqrt θ)) * K := @tight_plan_rate_real
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {ρ B θ : ℝ} {N : ℕ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hθ : 0 ≤ θ) (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ) (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (ζ.real univ)) (hz : 2048 * E.unresolved ≤ ρ) (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ) (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved) i) ≤ w i) (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved) i)),
    ENNReal.ofReal (min (ρ/2) (sqrt (planCertificate ρ (planRates B
      (planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
      (planTerminal hρ B E.unresolved)) w)))) ≤
      ENNReal.ofReal (1 + 8/5 * max 4096 (224000 * sqrt θ)) *
      ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B := @tight_quantile_plan_rate
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {ρ B : ℝ} {N : ℕ} (θ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (ζ.real univ)) (hz : ρ < 2048 * E.unresolved),
    ENNReal.ofReal (ρ/2) ≤
      ENNReal.ofReal (1 + 8/5 * max 4096 (224000 * sqrt θ)) *
      ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B := @tight_quantile_fallback_rate
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {ρ B θ κ r : ℝ} {N : ℕ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hθ : 0 ≤ θ) (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ) (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (ζ.real univ)) (hz : 2048 * E.unresolved ≤ ρ) (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ) (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved) i) ≤ w i) (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved) i)) (hκ : κ * sqrt 8 ≤ 6) (hr : r ≤ κ * sqrt (8 * min (ρ^2/4) (planCertificate ρ (planRates B (planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved)) w)))),
    ENNReal.ofReal r ≤
      ENNReal.ofReal (6 * (1 + 8/5 * max 4096 (224000 * sqrt θ))) *
      ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B := @tight_quantile_plan_radius
example : ∀ (ν : Measure Gap) {c : ℝ} (hc : 0 ≤ c) (h : ℝ),
    tailModulus (ENNReal.ofReal c • ν) h = c * tailModulus ν h := @tailModulus_smul
example : ∀ (σ : Measure Gap) {c : ℝ} (hc : 0 ≤ c),
    measureCostEntropy (ENNReal.ofReal c • σ) = ENNReal.ofReal c * measureCostEntropy σ := @scaled_measureCostEntropy
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] {z ρ B : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 1/2) (hB : 0 < B),
    ENNReal.ofReal (ρ/(1+sqrt B)) ≤ zeroSelection (zeroAtomLaw z η) ρ B := @zero_selection_floor
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {z₀ ρ B : ℝ} (hz0 : 0 ≤ z₀) (hzρ : z₀ < ρ) (hρ1 : ρ ≤ 1) (hB : 0 < B) (hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀)) (htail : τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀)) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B),
    zeroQuantileValue z₀ η ρ B =
      ENNReal.ofReal (min ρ (z₀ + ζ.real univ + budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) +
      budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal))) := @zero_split_value
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {z₀ ρ B : ℝ} (hz0 : 0 ≤ z₀) (hzρ : z₀ < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀)) (htail : τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀)) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B),
    ∃ K : ℝ, 0 ≤ K ∧ zeroSelection (zeroAtomLaw z₀ η) ρ B = ENNReal.ofReal K ∧
      ρ/(1+sqrt B) ≤ K ∧
      min ρ (z₀ + ζ.real univ + budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) +
      budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal)) ≤ 4 * K := @zero_split_comparison
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {z₀ ρ B θ : ℝ} {N : ℕ} (hz0 : 0 ≤ z₀) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hθ : 0 ≤ θ) (hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀)) (htail : τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀)) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) (hN : bandEdge N < quantileThreshold η (conditionalRarity ρ z₀)) (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (z₀ + ζ.real univ)) (hz : 2048 * E.unresolved ≤ ρ) (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ) (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved) i) ≤ w i) (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved) i)),
    ENNReal.ofReal (min (ρ/2) (sqrt (planCertificate ρ (planRates B
      (planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
      (planTerminal hρ B E.unresolved)) w)))) ≤
      ENNReal.ofReal (1 + 4 * max 4096 (224000 * sqrt θ)) *
      zeroSelection (zeroAtomLaw z₀ η) ρ B := @zero_atom_plan_rate
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {z₀ ρ B : ℝ} {N : ℕ} (θ : ℝ) (hz0 : 0 ≤ z₀) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀)) (htail : τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀)) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (z₀ + ζ.real univ)) (hz : ρ < 2048 * E.unresolved),
    ENNReal.ofReal (ρ/2) ≤
      ENNReal.ofReal (1 + 4 * max 4096 (224000 * sqrt θ)) *
      zeroSelection (zeroAtomLaw z₀ η) ρ B := @zero_atom_fallback_rate
example : ∀ {C C' : ℝ} (h : C ≤ C'),
    plannedCoefficient C ≤ plannedCoefficient C' := @plannedCoefficient_mono
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {z₀ ρ B : ℝ} {N : ℕ} (hz0 : 0 ≤ z₀) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀)) (htail : τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀)) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) (hN : bandEdge N < quantileThreshold η (conditionalRarity ρ z₀)) (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (z₀ + ζ.real univ)) (hz : 2048 * E.unresolved ≤ ρ) (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ) (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved) i) ≤ w i) (hup : ∀ i, w i ≤ 2 * sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved) i)),
    ENNReal.ofReal (min (ρ/2) (sqrt (planCertificate ρ (planRates B
      (planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
      (planTerminal hρ B E.unresolved)) w)))) ≤
      ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B := @zero_atom_plan_rate_dyadic
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {z₀ ρ B κ r : ℝ} {N : ℕ} (hz0 : 0 ≤ z₀) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀)) (htail : τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀)) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) (hN : bandEdge N < quantileThreshold η (conditionalRarity ρ z₀)) (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (z₀ + ζ.real univ)) (hz : 2048 * E.unresolved ≤ ρ) (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ) (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved) i) ≤ w i) (hup : ∀ i, w i ≤ 2 * sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved) i)) (hκ : κ * sqrt 8 ≤ 6) (hr : r ≤ κ * sqrt (8 * min (ρ^2/4) (planCertificate ρ (planRates B (planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved)) w)))),
    ENNReal.ofReal r ≤
      ENNReal.ofReal (6 * plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B := @zero_atom_plan_radius_dyadic
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
