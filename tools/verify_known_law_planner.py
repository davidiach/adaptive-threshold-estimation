"""Audit the known-law plan and the validity of its certificate.

Every definition and theorem of the five planner modules is restated in full,
so a changed definition, hypothesis or constant is an elaboration error, and
the transitive axioms of every declaration are reported. A declaration in
those modules that is not registered here is an error. Prints the kernel
report; writes nothing.
"""

import subprocess
from verify_blind_upper_components import (DECLARATION, FORBIDDEN, LEAN, strip_comments,
                                           validate_reports)

MODULE = "ThresholdHC.KnownLawPlanner.PlanCertificate"
SOURCES = [LEAN / "ThresholdHC/KnownLawPlanner" / (name + ".lean")
           for name in ("PlannedEstimator", "PlanFamily", "PlanAllocation", "PlanCaps",
                        "PlanCertificate")]
NAMES = [
    "plannedEstimator", "planned_work_bound", "planned_mse_bound", "planFamily",
    "planFamily_cost_bound", "planFamily_binary", "plan_level_error", "planFamily_bias",
    "planFamily_second", "planLevelWork", "planLevelPrice", "planFamily_work", "planFamily_price",
    "planCount", "planCount_pos", "planCount_work", "mul_sqrt_div", "div_sqrt_div",
    "planCount_variance_le", "EnvelopeVanishes", "searchCap", "searchCap_spec", "searchCap_min",
    "searchCaps", "searchCaps_spec", "searchCaps_succ_ge", "searchCaps_monotone",
    "one_le_searchCaps", "searchCaps_admissible", "eta_vanishes", "planCertificate",
    "planCertificate_nonneg", "planEstimator", "one_le_planLevelPrice", "plan_budget",
    "plan_squaredRisk", "plan_rareRisk", "SplitEnclosure", "SplitEnclosure.exact",
    "SplitEnclosure.price", "SplitEnclosure.planLevelPrice_le", "enclosed_plan_valid",
    "enclosed_plan_minimax", "planCost", "planRates", "planCost_pos", "planRates_coe",
    "searched_plan_valid", "planCertificate_le_of_weights",
]


def declared_names():
    """Every declaration of the five modules, after rejecting proof escapes."""
    found = []
    for path in SOURCES:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + path.name)
        found += DECLARATION.findall(source)
    return found


def audit_input():
    if sorted(declared_names()) != sorted(NAMES):
        raise ValueError("Unregistered or missing known-law planner declaration")
    source = """
import ThresholdHC.KnownLawPlanner.PlanCertificate
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Set Real
open scoped NNReal ENNReal BigOperators
open ThresholdHC.KnownLawPlanner
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailUpper
open ThresholdHC.EntropyTailAssembly ThresholdHC.ObservableSimulation ThresholdHC.RareAboveTwo
open ThresholdHC.EntropyTailExecution ThresholdHC.EntropyTailSampling

example : ∀ {J : ℕ} (r : Fin (J+1) → ℝ≥0) (D : Fin (J+1) → FiniteCall),
    plannedEstimator r D = poissonPlanEstimator r (fun i => scaleCall ((r i:ℝ)⁻¹) (D i)) := by
  intros; rfl
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (w : ℕ → ℝ≥0) (hw : HasSum w 1) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (κ : ℕ → ℕ) (l : ℕ),
    planFamily μ w hw hρ hρ1 κ l = scheduledCall μ w hw hρ hρ1 l (2 * κ l) := by
  intros; rfl
example : ∀ (τ : Measure Gap) (ρ Γ z : ℝ) (l k : ℕ), planLevelWork τ ρ Γ z l k =
    128*(l+1)*Γ + 6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ + 2*ordinaryCost τ (4 ^ k) + 2*z*4 ^ k :=
  fun _ _ _ _ _ _ => rfl
example : ∀ (τ : Measure Gap) (ρ Γ z : ℝ) (l k : ℕ), planLevelPrice τ ρ Γ z l k =
    min (2 * 4 ^ k) (planLevelWork τ ρ Γ z l k) := fun _ _ _ _ _ _ => rfl
example : ∀ {ι : Type*} [Fintype ι] (B : ℝ) (k w : ι → ℝ) (i : ι),
    planCount B k w i = B * w i / ∑ j, k j * w j := by
  intros; rfl
example : ∀ (e : ℝ → ℝ), EnvelopeVanishes e ↔
    ∀ ε : ℝ, 0 < ε → ∀ k₀ : ℕ, ∃ k : ℕ, k₀ ≤ k ∧ e (4 ^ k) ≤ ε := fun _ => Iff.rfl
example : ∀ (e : ℝ → ℝ) (he : EnvelopeVanishes e) (ε : ℝ) (hε : 0 < ε) (k₀ : ℕ),
    searchCap e he ε hε k₀ = Nat.find (he ε hε k₀) := fun _ _ _ _ _ => rfl
example : ∀ (e : ℝ → ℝ) (he : EnvelopeVanishes e) {ρ : ℝ} (hρ : 0 < ρ),
    searchCaps e he hρ 0 = searchCap e he (levelAccuracy ρ 0/8)
        (div_pos (levelAccuracy_pos hρ 0) (by norm_num)) 1 ∧
      ∀ l : ℕ, searchCaps e he hρ (l+1) = searchCap e he (levelAccuracy ρ (l+1)/8)
        (div_pos (levelAccuracy_pos hρ (l+1)) (by norm_num)) (searchCaps e he hρ l) := by
  intros; exact ⟨rfl, fun _ => rfl⟩
example : ∀ (ρ : ℝ) {J : ℕ} (r : Fin (J+1) → ℝ≥0), planCertificate ρ r =
    levelAccuracy ρ J ^ 2 + ∑ i : Fin (J+1), 17*levelAccuracy ρ i.val/(r i:ℝ) := by
  intros; rfl
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    [IsProbabilityMeasure (σ+τ+ζ)] {t ρ : ℝ} {N : ℕ} (ht : 0 < t)
    (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
    (κ : ℕ → ℕ) {J : ℕ} (r : Fin (J+1) → ℝ≥0),
    planEstimator σ τ ζ ht hs hN hρ hρ1 κ r =
      plannedEstimator r (fun i => incrementCall (planFamily (σ+τ+ζ) (referenceWeights σ)
        (referenceWeights_probability σ ht hs hN) hρ hρ1 κ) i.val) := by
  intros; rfl
example : ∀ (σ τ ζ : Measure Gap) (N : ℕ) (entropy tailInverse unresolved : ℝ)
    (resolvedError tailWork : ℝ → ℝ)
    (entropy_le : costEntropy (fun j : Fin N => bandCost σ j.val) ≤ entropy)
    (tailInverse_le : (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) ≤ tailInverse)
    (unresolved_le : ζ.real univ ≤ unresolved)
    (resolvedError_le : ∀ M : ℝ, eta (σ+τ) M ≤ resolvedError M)
    (tailWork_le : ∀ M : ℝ, ordinaryCost τ M ≤ tailWork M),
    SplitEnclosure σ τ ζ N :=
  fun _ _ _ _ entropy tailInverse unresolved resolvedError tailWork h1 h2 h3 h4 h5 =>
    ⟨entropy, tailInverse, unresolved, resolvedError, tailWork, h1, h2, h3, h4, h5⟩
example : ∀ (σ τ ζ : Measure Gap) (N : ℕ),
    (SplitEnclosure.exact σ τ ζ N).entropy = costEntropy (fun j : Fin N => bandCost σ j.val) ∧
    (SplitEnclosure.exact σ τ ζ N).tailInverse = (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) ∧
    (SplitEnclosure.exact σ τ ζ N).unresolved = ζ.real univ ∧
    (SplitEnclosure.exact σ τ ζ N).resolvedError = eta (σ+τ) ∧
    (SplitEnclosure.exact σ τ ζ N).tailWork = ordinaryCost τ :=
  fun _ _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
example : ∀ {σ τ ζ : Measure Gap} {N : ℕ} (E : SplitEnclosure σ τ ζ N) (ρ : ℝ) (l k : ℕ),
    E.price ρ l k = min (2 * 4 ^ k)
      (128*(l+1)*E.entropy + 6*E.tailInverse^2/ρ + 2*E.tailWork (4 ^ k) + 2*E.unresolved*4 ^ k) := by
  intros; rfl
example : ∀ {σ τ ζ : Measure Gap} {N : ℕ} (E : SplitEnclosure σ τ ζ N) (ρ : ℝ) (κ : ℕ → ℕ)
    (J : ℕ) (i : Fin (J+1)),
    planCost E ρ κ J i = adjacentCost (fun l => E.price ρ l (κ l)) i.val := by
  intros; rfl
example : ∀ {J : ℕ} (B : ℝ) (k w : Fin (J+1) → ℝ) (i : Fin (J+1)),
    planRates B k w i = Real.toNNReal (planCount B k w i) := by
  intros; rfl
example : ∀ {J : ℕ} (r : Fin (J+1) → ℝ≥0) (D : Fin (J+1) → FiniteCall) {K : Fin (J+1) → ℝ} (hK : ∀ i ω, ((D i).cost ω:ℝ) ≤ K i) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {c : Fin (J+1) → ℝ} (hC : ∀ i, (∫ ω, ((D i).cost ω:ℝ) ∂originalPopulationTapeLaw μ q) ≤ c i),
    expectedWork μ (plannedEstimator r D) q ≤ ENNReal.ofReal (∑ i, (r i:ℝ) * c i) := @planned_work_bound
example : ∀ {J : ℕ} (r : Fin (J+1) → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ)) (D : Fin (J+1) → FiniteCall) {U : Fin (J+1) → ℝ} (hU0 : ∀ i, 0 ≤ U i) (hU : ∀ i ω, ‖(D i).value ω‖ ≤ U i) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (a : ℝ) {v : Fin (J+1) → ℝ} (hV : ∀ i, (∫ ω, ((D i).value ω)^2 ∂originalPopulationTapeLaw μ q) ≤ v i) {b : ℝ} (hb : 0 ≤ b) (hbias : |(∑ i, ∫ ω, (D i).value ω ∂originalPopulationTapeLaw μ q)-a| ≤ b),
    squaredRisk (experimentLaw μ (plannedEstimator r D) q)
      (populationOutput (plannedEstimator r D)) a ≤
      ENNReal.ofReal ((∑ i, v i / (r i:ℝ)) + b^2) := @planned_mse_bound
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (w : ℕ → ℝ≥0) (hw : HasSum w 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (κ : ℕ → ℕ) (l : ℕ) (ω : ℕ → Bool),
    ((planFamily μ w hw hρ hρ1 κ l).cost ω:ℝ) ≤ 2 * 4 ^ κ l := @planFamily_cost_bound
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (w : ℕ → ℝ≥0) (hw : HasSum w 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (κ : ℕ → ℕ) (l : ℕ) (ω : ℕ → Bool),
    (planFamily μ w hw hρ hρ1 κ l).value ω = 0 ∨ (planFamily μ w hw hρ hρ1 κ l).value ω = 1 := @planFamily_binary
example : ∀ (μ ν ζ : Measure Gap) [IsProbabilityMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ζ] (hμ : μ = ν+ζ) (weights : ℕ → ℝ≥0) (hw : HasSum weights 1) {ρ : ℝ} (hρ : 0 < ρ) (q : SignLaw) (hq : RarePrior μ ρ q) (l k : ℕ) (hk : eta ν (4 ^ k) ≤ levelAccuracy ρ l/8) (hz : ζ.real Set.univ ≤ levelAccuracy ρ l/8),
    racePopulationError μ q (negativeBankTest weights (levelEpsilon l))
      (positiveBankTest μ weights (ρ*levelEpsilon l)) (2*k) ≤ levelAccuracy ρ l := @plan_level_error
example : ∀ (μ ν ζ : Measure Gap) [IsProbabilityMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ζ] (hμ : μ = ν+ζ) (w : ℕ → ℝ≥0) (hw : HasSum w 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (q : SignLaw) (hq : RarePrior μ ρ q) (κ : ℕ → ℕ) (l : ℕ) (hκ : eta ν (4 ^ κ l) ≤ levelAccuracy ρ l/8) (hz : ζ.real Set.univ ≤ levelAccuracy ρ l/8),
    |(∫ ω, (planFamily μ w hw hρ hρ1 κ l).value ω ∂originalPopulationTapeLaw μ q)-
      signMean μ q.val| ≤ levelAccuracy ρ l := @planFamily_bias
example : ∀ (μ ν ζ : Measure Gap) [IsProbabilityMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ζ] (hμ : μ = ν+ζ) (w : ℕ → ℝ≥0) (hw : HasSum w 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (q : SignLaw) (hq : RarePrior μ ρ q) (κ : ℕ → ℕ) (l : ℕ) (hκ : ∀ j, j ≤ l → eta ν (4 ^ κ j) ≤ levelAccuracy ρ j/8) (hz : ζ.real Set.univ ≤ levelAccuracy ρ l/8),
    (∫ ω, ((incrementCall (planFamily μ w hw hρ hρ1 κ) l).value ω)^2
      ∂originalPopulationTapeLaw μ q) ≤ 17*levelAccuracy ρ l := @planFamily_second
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : ThresholdHC.EntropyTailQuantile.bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hz : ζ.real Set.univ ≤ ρ) (q : SignLaw) (hq : RarePrior (σ+τ+ζ) ρ q) (κ : ℕ → ℕ) (l : ℕ),
    (∫ ω, ((planFamily (σ+τ+ζ) (referenceWeights σ)
      (referenceWeights_probability σ ht hs hN) hρ hρ1 κ l).cost ω:ℝ)
      ∂originalPopulationTapeLaw (σ+τ+ζ) q) ≤
      planLevelWork τ ρ (ThresholdHC.EntropyTailQuantile.costEntropy
      (fun j : Fin N => ThresholdHC.EntropyTailQuantile.bandCost σ j.val))
      (ζ.real Set.univ) l (κ l) := @planFamily_work
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : ThresholdHC.EntropyTailQuantile.bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hz : ζ.real Set.univ ≤ ρ) (q : SignLaw) (hq : RarePrior (σ+τ+ζ) ρ q) (κ : ℕ → ℕ) (l : ℕ),
    (∫ ω, ((planFamily (σ+τ+ζ) (referenceWeights σ)
      (referenceWeights_probability σ ht hs hN) hρ hρ1 κ l).cost ω:ℝ)
      ∂originalPopulationTapeLaw (σ+τ+ζ) q) ≤
      planLevelPrice τ ρ (ThresholdHC.EntropyTailQuantile.costEntropy
      (fun j : Fin N => ThresholdHC.EntropyTailQuantile.bandCost σ j.val))
      (ζ.real Set.univ) l (κ l) := @planFamily_price
example : ∀ {ι : Type*} [Fintype ι] [Nonempty ι] {B : ℝ} {k w : ι → ℝ} (hB : 0 < B) (hk : ∀ i, 0 < k i) (hw : ∀ i, 0 < w i) (i : ι),
    0 < planCount B k w i := @planCount_pos
example : ∀ {ι : Type*} [Fintype ι] [Nonempty ι] {B : ℝ} {k w : ι → ℝ} (hk : ∀ i, 0 < k i) (hw : ∀ i, 0 < w i),
    ∑ i, k i * planCount B k w i = B := @planCount_work
example : ∀ {v k : ℝ} (hv : 0 < v) (hk : 0 < k),
    k * sqrt (v / k) = sqrt (v * k) := @mul_sqrt_div
example : ∀ {v k : ℝ} (hv : 0 < v) (hk : 0 < k),
    v / sqrt (v / k) = sqrt (v * k) := @div_sqrt_div
example : ∀ {ι : Type*} [Fintype ι] [Nonempty ι] {B θ : ℝ} {v k w : ι → ℝ} (hB : 0 < B) (hv : ∀ i, 0 < v i) (hk : ∀ i, 0 < k i) (hlow : ∀ i, sqrt (v i / k i) ≤ w i) (hup : ∀ i, w i ≤ θ * sqrt (v i / k i)),
    ∑ i, v i / planCount B k w i ≤ θ * (allocationCertificate v k) ^ 2 / B := @planCount_variance_le
example : ∀ (e : ℝ → ℝ) (he : EnvelopeVanishes e) (ε : ℝ) (hε : 0 < ε) (k₀ : ℕ),
    k₀ ≤ searchCap e he ε hε k₀ ∧ e (4 ^ searchCap e he ε hε k₀) ≤ ε := @searchCap_spec
example : ∀ (e : ℝ → ℝ) (he : EnvelopeVanishes e) (ε : ℝ) (hε : 0 < ε) (k₀ : ℕ) {k : ℕ} (hk₀ : k₀ ≤ k) (hk : k < searchCap e he ε hε k₀),
    ε < e (4 ^ k) := @searchCap_min
example : ∀ (e : ℝ → ℝ) (he : EnvelopeVanishes e) {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ),
    e (4 ^ searchCaps e he hρ l) ≤ levelAccuracy ρ l/8 := @searchCaps_spec
example : ∀ (e : ℝ → ℝ) (he : EnvelopeVanishes e) {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ),
    searchCaps e he hρ l ≤ searchCaps e he hρ (l+1) := @searchCaps_succ_ge
example : ∀ (e : ℝ → ℝ) (he : EnvelopeVanishes e) {ρ : ℝ} (hρ : 0 < ρ),
    Monotone (searchCaps e he hρ) := @searchCaps_monotone
example : ∀ (e : ℝ → ℝ) (he : EnvelopeVanishes e) {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ),
    1 ≤ searchCaps e he hρ l := @one_le_searchCaps
example : ∀ (ν : Measure Gap) (e : ℝ → ℝ) (he : EnvelopeVanishes e) (hbound : ∀ M : ℝ, eta ν M ≤ e M) {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ),
    eta ν (4 ^ searchCaps e he hρ l) ≤ levelAccuracy ρ l/8 := @searchCaps_admissible
example : ∀ (ν : Measure Gap) [IsFiniteMeasure ν],
    EnvelopeVanishes (eta ν) := @eta_vanishes
example : ∀ {ρ : ℝ} (hρ : 0 < ρ) {J : ℕ} (r : Fin (J+1) → ℝ≥0),
    0 ≤ planCertificate ρ r := @planCertificate_nonneg
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hz : ζ.real univ ≤ ρ) (l k : ℕ),
    1 ≤ planLevelPrice τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val)) (ζ.real univ) l k := @one_le_planLevelPrice
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hz : ζ.real univ ≤ ρ) (κ : ℕ → ℕ) (C : ℕ → ℝ) (hC : ∀ l, planLevelPrice τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val)) (ζ.real univ) l (κ l) ≤ C l) {J : ℕ} (r : Fin (J+1) → ℝ≥0) (hwork : ∑ i : Fin (J+1), (r i:ℝ) * adjacentCost C i.val ≤ B),
    RareBudget (σ+τ+ζ) (planEstimator σ τ ζ ht hs hN hρ hρ1 κ r) ρ B := @plan_budget
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (κ : ℕ → ℕ) {J : ℕ} (hκ : ∀ l, l ≤ J → eta (σ+τ) (4 ^ κ l) ≤ levelAccuracy ρ l/8) (hzJ : ζ.real univ ≤ levelAccuracy ρ J/8) (r : Fin (J+1) → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ)) (q : SignLaw) (hq : RarePrior (σ+τ+ζ) ρ q),
    squaredRisk (experimentLaw (σ+τ+ζ) (planEstimator σ τ ζ ht hs hN hρ hρ1 κ r) q)
      (populationOutput (planEstimator σ τ ζ ht hs hN hρ hρ1 κ r)) (signMean (σ+τ+ζ) q.val) ≤
      ENNReal.ofReal (planCertificate ρ r) := @plan_squaredRisk
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (κ : ℕ → ℕ) {J : ℕ} (hκ : ∀ l, l ≤ J → eta (σ+τ) (4 ^ κ l) ≤ levelAccuracy ρ l/8) (hzJ : ζ.real univ ≤ levelAccuracy ρ J/8) (r : Fin (J+1) → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ)),
    rareRisk (σ+τ+ζ) (planEstimator σ τ ζ ht hs hN hρ hρ1 κ r) ρ ≤
      ENNReal.ofReal (Real.sqrt (planCertificate ρ r)) := @plan_rareRisk
example : ∀ {σ τ ζ : Measure Gap} {N : ℕ} (E : SplitEnclosure σ τ ζ N) {ρ : ℝ} (hρ : 0 < ρ) (l k : ℕ),
    planLevelPrice τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val)) (ζ.real univ) l k ≤
      E.price ρ l k := @SplitEnclosure.planLevelPrice_le
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (E : SplitEnclosure σ τ ζ N) (κ : ℕ → ℕ) {J : ℕ} (hκ : ∀ l, l ≤ J → E.resolvedError (4 ^ κ l) ≤ levelAccuracy ρ l/8) (hzJ : E.unresolved ≤ levelAccuracy ρ J/8) (r : Fin (J+1) → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ)) (hwork : ∑ i : Fin (J+1), (r i:ℝ) * adjacentCost (fun l => E.price ρ l (κ l)) i.val ≤ B),
    RareBudget (σ+τ+ζ) (planEstimator σ τ ζ ht hs hN hρ hρ1 κ r) ρ B ∧
      rareRisk (σ+τ+ζ) (planEstimator σ τ ζ ht hs hN hρ hρ1 κ r) ρ ≤
      ENNReal.ofReal (Real.sqrt (planCertificate ρ r)) := @enclosed_plan_valid
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (E : SplitEnclosure σ τ ζ N) (κ : ℕ → ℕ) {J : ℕ} (hκ : ∀ l, l ≤ J → E.resolvedError (4 ^ κ l) ≤ levelAccuracy ρ l/8) (hzJ : E.unresolved ≤ levelAccuracy ρ J/8) (r : Fin (J+1) → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ)) (hwork : ∑ i : Fin (J+1), (r i:ℝ) * adjacentCost (fun l => E.price ρ l (κ l)) i.val ≤ B),
    rareMinimaxRisk (σ+τ+ζ) ρ B ≤
      ENNReal.ofReal (min (ρ/2) (Real.sqrt (planCertificate ρ r))) := @enclosed_plan_minimax
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hz : ζ.real univ ≤ ρ) (E : SplitEnclosure σ τ ζ N) (κ : ℕ → ℕ) (J : ℕ) (i : Fin (J+1)),
    0 < planCost E ρ κ J i := @planCost_pos
example : ∀ {J : ℕ} {B : ℝ} {k w : Fin (J+1) → ℝ} (hB : 0 < B) (hk : ∀ i, 0 < k i) (hw : ∀ i, 0 < w i) (i : Fin (J+1)),
    (planRates B k w i:ℝ) = planCount B k w i := @planRates_coe
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 < B) (E : SplitEnclosure σ τ ζ N) (hvan : EnvelopeVanishes E.resolvedError) {J : ℕ} (hzJ : E.unresolved ≤ levelAccuracy ρ J/8) (w : Fin (J+1) → ℝ) (hw : ∀ i, 0 < w i),
    RareBudget (σ+τ+ζ) (planEstimator σ τ ζ ht hs hN hρ hρ1
      (searchCaps E.resolvedError hvan hρ)
      (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w)) ρ B ∧
      rareRisk (σ+τ+ζ) (planEstimator σ τ ζ ht hs hN hρ hρ1
      (searchCaps E.resolvedError hvan hρ)
      (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w)) ρ ≤
      ENNReal.ofReal (Real.sqrt (planCertificate ρ
      (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w))) := @searched_plan_valid
example : ∀ {ρ B θ : ℝ} (hρ : 0 < ρ) (hB : 0 < B) {J : ℕ} {k w : Fin (J+1) → ℝ} (hk : ∀ i, 0 < k i) (hlow : ∀ i, Real.sqrt (17*levelAccuracy ρ i.val / k i) ≤ w i) (hup : ∀ i, w i ≤ θ * Real.sqrt (17*levelAccuracy ρ i.val / k i)),
    planCertificate ρ (planRates B k w) ≤
      levelAccuracy ρ J ^ 2 +
      θ * (allocationCertificate (fun i : Fin (J+1) => 17*levelAccuracy ρ i.val) k) ^ 2 / B := @planCertificate_le_of_weights
"""
    if source.count("example ") != len(NAMES):
        raise ValueError("Each planner declaration needs exactly one restated statement")
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
