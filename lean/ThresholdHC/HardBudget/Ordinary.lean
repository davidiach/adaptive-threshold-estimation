import ThresholdHC.HardBudget.BudgetScale
import ThresholdHC.Tier6.Full

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.HardBudget
open ThresholdHC.Tier6 ThresholdHC.BlindUpper

def hardMinimaxRisk (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    PathwiseCap A ⌊B⌋₊ ∧ t = maximalRMSRisk μ A}

/-- The same hard-cap rule works before the gap law is known. -/
theorem ordinary_hard_family : ∃ rule : ℝ → AdaptiveEstimator (ℕ → BatchSeed),
    (∀ B : ℝ, 0 ≤ B → PathwiseCap (rule B) ⌊B⌋₊) ∧
    ∀ (B : ℝ), 0 < B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      maximalRMSRisk μ (rule B) ≤ ENNReal.ofReal (3000*modulus μ (1/Real.sqrt B)) := by
  let base (j : ℕ) := budgetEstimator (stageAllowance j)
  obtain ⟨rule,hcap,hr⟩ := rms_family base 1 (by norm_num)
  refine ⟨rule,hcap,?_⟩
  intro B hB μ _
  apply iSup_le
  intro q
  apply hr B hB μ q 512 3000 (fun b => modulus μ (1/Real.sqrt b)) (signMean_bounds μ q).2
    (by norm_num) (by norm_num) (by norm_num)
  · intro b _; exact modulus_nonneg μ (by positivity)
  · intro b hb hu; exact modulus_eq_one_of_half_le μ (half_le_inverse_sqrt hb hu)
  · intro b b' hb hbb; exact ordinary_budget_scale μ (by linarith) hbb
  · intro j
    have hj : 1 ≤ (stageAllowance j:ℝ) := by simpa only [stageAllowance,Nat.cast_pow,Nat.cast_ofNat] using (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j))
    exact ⟨by simpa only [ENNReal.ofReal_natCast] using budgetEstimator_uniformBudget (stageAllowance j) μ q,
      (le_iSup (fun u => rootMeanRisk (experimentLaw μ (base j) u) (populationOutput (base j))
        (signMean μ u.val)) q).trans (budgetEstimator_maximalRMSRisk (stageAllowance j) hj μ)⟩

theorem ordinary_hard_minimax (μ : Measure Gap) [IsProbabilityMeasure μ] {B : ℝ} (hB : 1 ≤ B) :
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/64) ≤ hardMinimaxRisk μ B ∧
      hardMinimaxRisk μ B ≤ ENNReal.ofReal (3000*modulus μ (1/Real.sqrt B)) := by
  obtain ⟨rule,hc,hr⟩ := ordinary_hard_family
  constructor
  · apply le_sInf
    rintro t ⟨R,mR,A,hA,rfl⟩
    exact (minimax_lower_bound μ B hB).trans (sInf_le ⟨R,mR,A,fun q => pathwise_expected μ A q (by linarith) hA,rfl⟩)
  · apply le_trans _ (hr B (by linarith) μ)
    apply sInf_le
    exact ⟨ℕ → BatchSeed,inferInstance,rule B,hc B (by linarith),rfl⟩

end ThresholdHC.HardBudget
