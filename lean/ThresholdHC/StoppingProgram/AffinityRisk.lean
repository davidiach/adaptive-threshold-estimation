import ThresholdHC.StoppingProgram.AffinityOverlap
import ThresholdHC.Tier6.RiskReduction

/-! Sharp squared-loss testing by affinity for arbitrary measurable
estimators, allowing infinite risk and non-equivalent endpoint measures. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy ThresholdHC.UnbiasedConverse ThresholdHC.Tier6

theorem density_squared_loss (p q x a b : ℝ) (hs : p+q = 1) :
    (b-a)^2*(p*q) ≤ p*(x-a)^2+q*(x-b)^2 := by
  calc
    _ ≤ (b-a)^2*(p*q)+(p*(x-a)+q*(x-b))^2 := le_add_of_nonneg_right (sq_nonneg _)
    _ = (p+q)*(p*(x-a)^2+q*(x-b)^2) := by ring
    _ = _ := by rw [hs,one_mul]

theorem squared_loss_overlap_integral {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Ω → ℝ) (a b : ℝ)
    (hP : Integrable (fun x => (f x-a)^2) P) (hQ : Integrable (fun x => (f x-b)^2) Q) :
    (b-a)^2*(∫ x, overlapDensity P Q x ∂(P+Q)) ≤
      (∫ x, (f x-a)^2 ∂P)+(∫ x, (f x-b)^2 ∂Q) := by
  have hp : P ≪ P+Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hq : Q ≪ P+Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  have hiP := (integrable_toReal_rnDeriv_mul_iff hp).mpr hP
  have hiQ := (integrable_toReal_rnDeriv_mul_iff hq).mpr hQ
  have hh := integral_mono_ae ((integrable_overlapDensity P Q).const_mul ((b-a)^2)) (hiP.add hiQ)
    (by
      filter_upwards [comparisonDensity_sum P Q] with x hx
      simp only [comparisonDensity,add_comm Q P] at hx
      exact density_squared_loss _ _ (f x) a b hx)
  simp only [Pi.add_apply] at hh
  rw [integral_const_mul,integral_add hiP hiQ,
    integral_toReal_rnDeriv_mul hp,integral_toReal_rnDeriv_mul hq] at hh
  exact hh

theorem affinity_squared_risk {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Ω → ℝ) (hf : Measurable f) (a b : ℝ) :
    ENNReal.ofReal ((b-a)^2*(hellingerAffinity P Q).toReal^2/4) ≤
      max (squaredRisk P f a) (squaredRisk Q f b) := by
  by_cases hPtop : squaredRisk P f a = ⊤
  · rw [hPtop,max_eq_left le_top]
    exact le_top
  by_cases hQtop : squaredRisk Q f b = ⊤
  · rw [hQtop,max_eq_right le_top]
    exact le_top
  have hPm : AEStronglyMeasurable (fun x => (f x-a)^2) P := (by fun_prop : Measurable _).aestronglyMeasurable
  have hQm : AEStronglyMeasurable (fun x => (f x-b)^2) Q := (by fun_prop : Measurable _).aestronglyMeasurable
  have hPi : Integrable (fun x => (f x-a)^2) P :=
    (lintegral_ofReal_ne_top_iff_integrable hPm (Filter.Eventually.of_forall (fun x => sq_nonneg _))).mp hPtop
  have hQi : Integrable (fun x => (f x-b)^2) Q :=
    (lintegral_ofReal_ne_top_iff_integrable hQm (Filter.Eventually.of_forall (fun x => sq_nonneg _))).mp hQtop
  have hPr : squaredRisk P f a = ENNReal.ofReal (∫ x, (f x-a)^2 ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hPi (Filter.Eventually.of_forall (fun x => sq_nonneg _))).symm
  have hQr : squaredRisk Q f b = ENNReal.ofReal (∫ x, (f x-b)^2 ∂Q) :=
    (ofReal_integral_eq_lintegral_ofReal hQi (Filter.Eventually.of_forall (fun x => sq_nonneg _))).symm
  have hcs := mul_le_mul_of_nonneg_left (affinity_sq_le_overlap P Q) (sq_nonneg (b-a))
  have hr := squared_loss_overlap_integral P Q f a b hPi hQi
  have hreal : (b-a)^2*(hellingerAffinity P Q).toReal^2/4 ≤
      max (∫ x, (f x-a)^2 ∂P) (∫ x, (f x-b)^2 ∂Q) := by
    have hl := le_max_left (∫ x, (f x-a)^2 ∂P) (∫ x, (f x-b)^2 ∂Q)
    have hh := le_max_right (∫ x, (f x-a)^2 ∂P) (∫ x, (f x-b)^2 ∂Q)
    nlinarith [hcs,hr]
  rw [hPr,hQr,← ENNReal.ofReal_max]
  exact ENNReal.ofReal_le_ofReal hreal

theorem affinity_rms_risk {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Ω → ℝ) (hf : Measurable f) (a b : ℝ) (hab : a ≤ b) :
    ENNReal.ofReal ((b-a)*(hellingerAffinity P Q).toReal/2) ≤
      max (rootMeanRisk P f a) (rootMeanRisk Q f b) := by
  have h := ENNReal.rpow_le_rpow (affinity_squared_risk P Q f hf a b) (by norm_num : (0:ℝ) ≤ 1/2)
  rw [ENNReal.max_rpow (by norm_num : (0:ℝ) ≤ 1/2)] at h
  have he : (b-a)^2*(hellingerAffinity P Q).toReal^2/4 =
      ((b-a)*(hellingerAffinity P Q).toReal/2)^2 := by ring
  rw [he,ofReal_square_rpow_half _ (by positivity)] at h
  exact h

end ThresholdHC.StoppingProgram
