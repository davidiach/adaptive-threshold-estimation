import ThresholdHC.ConfidenceProgram.Amplify
import ThresholdHC.ConfidenceProgram.Schedule
import ThresholdHC.ConfidenceProgram.Lower
import ThresholdHC.ConfidenceTransfer.CriticalRate
import ThresholdHC.HardBudget.Rare
import ThresholdHC.HardBudget.Critical

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ConfidenceProgram
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.HardBudget ThresholdHC.EntropyTail
open ThresholdHC.ConfidenceTransfer ThresholdHC.CriticalUpper

/-- Uniform confidence radius with a cap on every valid observable path. -/
def hardConfidenceRadius (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B δ : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R) (r : ℝ),
    0 ≤ r ∧ PathwiseCap A ⌊B⌋₊ ∧
    (∀ q : SignLaw, RarePrior μ ρ q → ThresholdHC.Confidence.failureProbability μ A q r ≤ ENNReal.ofReal δ) ∧
    t = ENNReal.ofReal r}

theorem expected_confidence_le_hard (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B δ : ℝ} (hB : 0 ≤ B) :
    rareConfidenceRadius μ ρ B δ ≤ hardConfidenceRadius μ ρ B δ := by
  apply le_sInf
  rintro t ⟨R,mR,A,ε,hε,hcap,hf,rfl⟩
  apply sInf_le
  exact ⟨R,mR,A,ε,hε,fun q _ => pathwise_expected μ A q hB hcap,hf,rfl⟩

theorem hard_confidence_of_base {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) {ρ B δ r : ℝ}
    (hb : 0 < B) (hd : 0 < δ) (hr : 0 ≤ r) (hw : RareBudget μ A ρ (baseBudget B δ))
    (hR : rareRisk μ A ρ ≤ ENNReal.ofReal r) :
    hardConfidenceRadius μ ρ B δ ≤ ENNReal.ofReal (Real.sqrt 8*r) := by
  let m := groups δ
  let N := ⌊B/(2*(m:ℝ)+1)⌋₊
  apply sInf_le
  refine ⟨ℕ → R,inferInstance,cappedMedian A m N ρ,Real.sqrt 8*r,mul_nonneg (Real.sqrt_nonneg _) hr,
    median_budget_cap A m hb ρ,?_,rfl⟩
  intro q hq
  have h := hard_median_transfer μ A q m hb ⟨(signMean_bounds μ q).1,hq⟩ hr (hw q hq)
    ((rms_le_rare μ A ρ q hq).trans hR)
  exact h.2.trans (ENNReal.ofReal_le_ofReal (schedule_failure hd))

private theorem amplified_scale (C x y a : ℝ) (hC : 0 ≤ C) (hy : 0 ≤ y)
    (ha : a ≤ Real.sqrt 88) (hx : x ≤ a*y) :
    Real.sqrt 8*(C*x) ≤ (267/10)*C*y := by
  have hs : Real.sqrt 8*Real.sqrt 88 ≤ (267/10:ℝ) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8)]
    apply Real.sqrt_le_iff.mpr
    norm_num
  calc Real.sqrt 8*(C*x) ≤ Real.sqrt 8*(C*(Real.sqrt 88*y)) :=
         mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hx.trans (mul_le_mul_of_nonneg_right ha hy)) hC) (Real.sqrt_nonneg _)
       _ = (Real.sqrt 8*Real.sqrt 88)*C*y := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hC) hy

theorem general_hard_confidence_upper (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B δ : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hb : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    hardConfidenceRadius μ ρ B δ ≤ 750000*selection μ ρ (B/Real.log (1/δ)) := by
  let b := baseBudget B δ
  let β := B/Real.log (1/δ)
  obtain ⟨hb',horder,hscale⟩ := baseBudget_scale hb hd hd'
  obtain ⟨R,mR,A,hw,hR⟩ := rare_base μ hr hu hb'
  have h := hard_confidence_of_base μ A hb hd (by positivity : 0 ≤ 28001*(selection μ ρ b).toReal) hw hR
  have hg := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (finite_selection μ ρ β))
    (selection_budget_scale μ ρ hb' horder)
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hg
  have hc := amplified_scale 28001 _ _ _ (by norm_num) ENNReal.toReal_nonneg hscale hg
  have hfinal : Real.sqrt 8*(28001*(selection μ ρ b).toReal) ≤ 750000*(selection μ ρ β).toReal :=
    hc.trans (by nlinarith only [ENNReal.toReal_nonneg (a := selection μ ρ β)])
  apply h.trans
  have he := ENNReal.ofReal_le_ofReal hfinal
  rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (750000:ℝ)),ENNReal.ofReal_toReal (finite_selection _ _ _)] at he
  simpa only [ENNReal.ofReal_ofNat] using he

theorem critical_hard_confidence_upper {ρ B δ : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hb : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    hardConfidenceRadius criticalPositiveLaw ρ B δ ≤
      ENNReal.ofReal (2670000*criticalRate ρ (B/Real.log (1/δ))) := by
  let b := baseBudget B δ
  let β := B/Real.log (1/δ)
  obtain ⟨hb',horder,hscale⟩ := baseBudget_scale hb hd hd'
  let A := criticalBudgetEstimator ρ b
  have hw := (critical_budget_equivalence A ρ b).mp (criticalBudget_uniformBudget ρ hr (by linarith) b)
  have hR := criticalBudget_maximalRMSRisk ρ hr (by linarith) b hb'
  rw [critical_risk_equivalence] at hR
  have hp (b : ℝ) : 0 ≤ criticalRate ρ b := le_min hr.le (Real.sqrt_nonneg _)
  have h := hard_confidence_of_base criticalPositiveLaw A hb hd
    (mul_nonneg (by norm_num : 0 ≤ (100000:ℝ)) (hp b)) hw hR
  have hsc := amplified_scale 100000 _ _ _ (by norm_num) (hp β) hscale (critical_rate_scale hr hu hb' horder)
  apply h.trans; apply ENNReal.ofReal_le_ofReal
  linarith only [hsc]

theorem general_confidence_rate (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B δ : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hb : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    let K := selection μ ρ (B/Real.log (1/δ))
    ENNReal.ofReal ((10:ℝ)⁻¹^17)*K/30 ≤ rareConfidenceRadius μ ρ B δ ∧
    rareConfidenceRadius μ ρ B δ ≤ hardConfidenceRadius μ ρ B δ ∧ hardConfidenceRadius μ ρ B δ ≤ 750000*K :=
  ⟨entropy_tail_confidence_lower μ hr hu hb hd hd',expected_confidence_le_hard μ hb.le,
    general_hard_confidence_upper μ hr hu hb hd hd'⟩

theorem critical_confidence_rate :
    ∃ c : ℝ, 0 < c ∧ ∀ (ρ B δ : ℝ), 0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < δ → δ ≤ 1/4 →
    let z := min ρ (Real.sqrt (ρ*ThresholdHC.CriticalEntropy.criticalLogFactor ρ*Real.log (1/δ)/B))
    ENNReal.ofReal (c*z) ≤ rareConfidenceRadius criticalPositiveLaw ρ B δ ∧
    rareConfidenceRadius criticalPositiveLaw ρ B δ ≤ hardConfidenceRadius criticalPositiveLaw ρ B δ ∧
    hardConfidenceRadius criticalPositiveLaw ρ B δ ≤ ENNReal.ofReal (2670000*z) := by
  obtain ⟨c,hc,hlo⟩ := critical_confidence_lower
  refine ⟨c,hc,?_⟩
  intro ρ B δ hr hu hb hd hd'
  refine ⟨hlo ρ B δ hr hu hb hd hd',expected_confidence_le_hard _ hb.le,?_⟩
  have h := critical_hard_confidence_upper hr hu hb hd hd'
  simpa only [criticalRate,div_div_eq_mul_div] using h

end ThresholdHC.ConfidenceProgram
