import ThresholdHC.SubcriticalPower.Sublinear
import ThresholdHC.BlindUpper.Full
import ThresholdHC.RareAboveTwo.Budget
import ThresholdHC.Confidence.Full

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.SubcriticalPower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.BlindUpper ThresholdHC.Confidence
open ThresholdHC.EntropyTailQuantile

private theorem saturated {C α ρ : ℝ} (hC : 1 ≤ C) (hα : 0 < α) (hu : α < 1) (hr : 0 ≤ ρ) :
    ρ/2 ≤ (C/(1-α))*ρ := by
  have h : 1 ≤ C/(1-α) := (one_le_div (by linarith)).mpr (by linarith)
  exact (by linarith : ρ/2 ≤ ρ).trans (le_mul_of_one_le_left hr h)

/-- The estimator is chosen before the actual gap law. The only law
information used in choosing the saturation branch is the margin envelope. -/
theorem sublinear_rms_family {α a ρ B : ℝ}
    (hα : 0 < α) (hu : α < 1) (ha : 0 < a) (hr : 0 ≤ ρ) (hb : 1 ≤ B) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerMargin ν α a →
      RareBudget ν A ρ B ∧ rareRisk ν A ρ ≤
        ENNReal.ofReal ((512/(1-α))*min ρ ((EntropyTailQuantile.budgetScale B/a)^α)) := by
  have hB : 0 < B := by linarith
  have hh : 0 < EntropyTailQuantile.budgetScale B := inv_pos.mpr (Real.sqrt_pos.mpr hB)
  by_cases hc : ρ ≤ (EntropyTailQuantile.budgetScale B/a)^α
  · refine ⟨_,inferInstance,idleEstimator ρ,?_⟩
    intro ν _ _
    refine ⟨fun q _ => (idle_work ν q ρ).le.trans bot_le,?_⟩
    rw [min_eq_left hc]
    exact (idle_risk ν ρ).trans (ENNReal.ofReal_le_ofReal (saturated (by norm_num) hα hu hr))
  · refine ⟨_,inferInstance,budgetEstimator B,?_⟩
    intro ν _ hm
    refine ⟨fun q _ => budgetEstimator_uniformBudget B ν q,?_⟩
    apply iSup_le; intro q; apply iSup_le; intro _
    have hR := (le_iSup (fun q : SignLaw => rootMeanRisk (experimentLaw ν (budgetEstimator B) q)
      (populationOutput (budgetEstimator B)) (signMean ν q.val)) q).trans (budgetEstimator_maximalRMSRisk B hb ν)
    apply hR.trans
    rw [min_eq_right (le_of_not_ge hc)]
    apply ENNReal.ofReal_le_ofReal
    have hs := sublinear_modulus ν hm ha hα hu hh
    rw [one_div]
    calc 512*modulus ν (EntropyTailQuantile.budgetScale B) ≤ 512*((EntropyTailQuantile.budgetScale B/a)^α/(1-α)) :=
           mul_le_mul_of_nonneg_left hs (by norm_num)
         _ = _ := by ring

theorem sublinear_confidence_family {α a ρ B δ : ℝ}
    (hα : 0 < α) (hu : α < 1) (ha : 0 < a) (hr : 0 ≤ ρ) (hb : 1 ≤ B)
    (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerMargin ν α a →
      RareBudget ν A ρ B ∧ ∀ q : SignLaw, RarePrior ν ρ q →
        failureProbability ν A q ((8192/(1-α))*min ρ ((confidenceScale B δ/a)^α)) ≤ ENNReal.ofReal δ := by
  let h := confidenceScale B δ
  have hh : 0 < h := confidenceScale_pos (by linarith) hd hd'
  by_cases hc : ρ ≤ (h/a)^α
  · refine ⟨_,inferInstance,idleEstimator ρ,?_⟩
    intro ν _ _
    refine ⟨fun q _ => (idle_work ν q ρ).le.trans bot_le,?_⟩
    intro q hq
    rw [min_eq_left hc]
    have hlo := (signMean_bounds ν q).1
    change signMean ν q.val ≤ ρ at hq
    have hab : |ρ/2-signMean ν q.val| ≤ ρ/2 := abs_le.mpr (by constructor <;> linarith)
    have hall := hab.trans (saturated (by norm_num : 1 ≤ (8192:ℝ)) hα hu hr)
    unfold failureProbability
    apply le_trans (b := 0) _ bot_le
    rw [show {z | (8192/(1-α))*ρ < |populationOutput (idleEstimator ρ) z-signMean ν q.val|} = ∅ from
      eq_empty_iff_forall_notMem.mpr (fun _ hz => hall.not_gt hz),measure_empty]
  · obtain ⟨R,mR,rule,hA⟩ := confidence_upper
    refine ⟨R,mR,rule B δ,?_⟩
    intro ν _ hm
    obtain ⟨hw,hf⟩ := hA B δ hb hd hd' ν
    refine ⟨fun q _ => hw q,?_⟩
    intro q _
    apply (failureProbability_mono ν _ q ?_).trans (hf q)
    rw [min_eq_right (le_of_not_ge hc)]
    calc 8192*modulus ν h ≤ 8192*((h/a)^α/(1-α)) :=
           mul_le_mul_of_nonneg_left (sublinear_modulus ν hm ha hα hu hh) (by norm_num)
         _ = _ := by ring

end ThresholdHC.SubcriticalPower
