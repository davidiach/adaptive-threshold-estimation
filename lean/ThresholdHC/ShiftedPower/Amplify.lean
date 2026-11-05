import ThresholdHC.Confidence.Full
import ThresholdHC.ConfidenceProgram.Amplify
import ThresholdHC.ConfidenceProgram.Schedule
import ThresholdHC.HardBudget.RareModel

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ShiftedPower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.Confidence ThresholdHC.HardBudget ThresholdHC.ConfidenceProgram

/-- A family with one uniform margin guarantee at each budget yields a
hard-cap confidence family before the actual law is supplied. -/
theorem amplify_margin {α a ρ C B δ : ℝ} (f : ℝ → ℝ)
    (hC : 0 ≤ C) (hB : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4)
    (hf : ∀ b, 0 < b → 0 ≤ f b)
    (hscale : ∀ b b', 0 < b → b ≤ b' → f b ≤ Real.sqrt (b'/b)*f b')
    (hbase : ∀ b : ℝ, 0 < b → ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerMargin ν α a →
        RareBudget ν A ρ b ∧ rareRisk ν A ρ ≤ ENNReal.ofReal (C*f b)) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R), PathwiseCap A ⌊B⌋₊ ∧
    ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerMargin ν α a →
      RareBudget ν A ρ B ∧ ∀ q : SignLaw, RarePrior ν ρ q →
        failureProbability ν A q (27*C*f (B/Real.log (1/δ))) ≤ ENNReal.ofReal δ := by
  let b := baseBudget B δ
  let β := B/Real.log (1/δ)
  let m := groups δ
  let n := ⌊B/(2*(m:ℝ)+1)⌋₊
  obtain ⟨hb,hbβ,hratio⟩ := baseBudget_scale hB hd hd'
  obtain ⟨R,mR,A,hA⟩ := hbase b hb
  let D := cappedMedian A m n ρ
  have hcap : PathwiseCap D ⌊B⌋₊ := median_budget_cap A m hB ρ
  refine ⟨ℕ → R,inferInstance,D,hcap,?_⟩
  intro ν _ hm
  obtain ⟨hw,hR⟩ := hA ν hm
  refine ⟨fun q _ => pathwise_expected ν D q hB.le hcap,?_⟩
  intro q hq
  have hc : 0 ≤ C*f b := mul_nonneg hC (hf b hb)
  have h := hard_median_transfer ν A q m hB ⟨(signMean_bounds ν q).1,hq⟩ hc (hw q hq)
    ((rms_le_rare ν A ρ q hq).trans hR)
  have hfail := h.2.trans (ENNReal.ofReal_le_ofReal (schedule_failure hd))
  apply (failureProbability_mono ν D q ?_).trans hfail
  have hβ : 0 < β := hb.trans_le hbβ
  have hff := (hscale b β hb hbβ).trans (mul_le_mul_of_nonneg_right hratio (hf β hβ))
  have hnum : Real.sqrt 8*Real.sqrt 88 ≤ (27:ℝ) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8)]
    exact Real.sqrt_le_iff.mpr (by norm_num)
  calc Real.sqrt 8*(C*f b) ≤ Real.sqrt 8*(C*(Real.sqrt 88*f β)) :=
         mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hff hC) (Real.sqrt_nonneg _)
       _ = (Real.sqrt 8*Real.sqrt 88)*C*f β := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnum hC) (hf β hβ)

end ThresholdHC.ShiftedPower
