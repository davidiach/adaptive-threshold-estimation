import ThresholdHC.CapIdentification.BudgetLimit
import ThresholdHC.CapIdentification.StoppedMatching
import ThresholdHC.CapIdentification.InformationZero

/-! The fixed-cap identification theorem: attained matching diameter,
exact infinite-budget bias floor, and finite/infinite support cases.
This is a theorem about the finite-cap program, not a floor on unrestricted
adaptive estimation with a growing cap. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.StoppingProgram ThresholdHC.RareAboveTwo

theorem programValue_budget_limit (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 ≤ ρ) {N : ℕ} (hN : 0 < N) :
    Tendsto (fun B : ℝ => programValue μ ρ B N) atTop
      (𝓝 (ENNReal.ofReal (capDiameter μ ρ N/2))) := by
  have ht := (programSquared_budget_limit μ hρ hN).ennrpow_const (1/(2:ℝ))
  have he : (ENNReal.ofReal ((capDiameter μ ρ N/2)^2))^(1/(2:ℝ)) =
      ENNReal.ofReal (capDiameter μ ρ N/2) := by
    rw [ENNReal.ofReal_pow (div_nonneg (capDiameter_bounds μ hρ N).1 (by norm_num))]
    simpa only [Nat.cast_ofNat,one_div] using ENNReal.pow_rpow_inv_natCast (n := 2)
      (by norm_num) (ENNReal.ofReal (capDiameter μ ρ N/2))
  simpa only [programValue,he] using ht

theorem fixed_cap_identification (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ) (hN : 0 < N) :
    (∃ qH qL : SignLaw, RarePrior μ ρ qH ∧ RarePrior μ ρ qL ∧ OddMomentMatch μ qH qL N ∧
      capDiameter μ ρ N = signMean μ qH.val-signMean μ qL.val ∧
      ∀ rH rL : SignLaw, RarePrior μ ρ rH → RarePrior μ ρ rL → OddMomentMatch μ rH rL N →
        signMean μ rH.val-signMean μ rL.val ≤ capDiameter μ ρ N) ∧
    Tendsto (fun B : ℝ => programValue μ ρ B N) atTop (𝓝 (ENNReal.ofReal (capDiameter μ ρ N/2))) ∧
    (∀ S : Finset Gap, μ.support = (S:Set Gap) → 0 < S.card →
      (capDiameter μ ρ N = 0 ↔ 2*S.card-1 ≤ N)) ∧
    (μ.support.Infinite → 0 < capDiameter μ ρ N) :=
  ⟨capDiameter_attained μ hρ.le N,programValue_budget_limit μ hρ.le hN,
    fun S hS hc => finite_support_diameter_zero_iff μ ρ hρ hρ1 N S hS hc,
    fun hμ => infinite_support_diameter_pos μ hμ ρ hρ hρ1 N⟩

end ThresholdHC.CapIdentification
