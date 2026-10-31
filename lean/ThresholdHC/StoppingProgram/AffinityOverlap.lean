import ThresholdHC.UnbiasedConverse.TwoPoint
import ThresholdHC.CriticalEntropy.EventualAffinity

/-! Density overlap bounds the Hellinger affinity on arbitrary probability
spaces. Densities are allowed to vanish. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy ThresholdHC.UnbiasedConverse

def overlapDensity {Ω : Type} [MeasurableSpace Ω] (P Q : Measure Ω) (x : Ω) : ℝ :=
  (P.rnDeriv (P+Q) x).toReal*(Q.rnDeriv (P+Q) x).toReal

theorem overlapDensity_nonneg {Ω : Type} [MeasurableSpace Ω] (P Q : Measure Ω) (x : Ω) :
    0 ≤ overlapDensity P Q x := mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

theorem measurable_overlapDensity {Ω : Type} [MeasurableSpace Ω] (P Q : Measure Ω) :
    Measurable (overlapDensity P Q) :=
  (Measure.measurable_rnDeriv P (P+Q)).ennreal_toReal.mul (Measure.measurable_rnDeriv Q (P+Q)).ennreal_toReal

theorem overlapDensity_le_one {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    ∀ᵐ x ∂(P+Q), overlapDensity P Q x ≤ 1 := by
  filter_upwards [comparisonDensity_sum P Q] with x hx
  have hp : 0 ≤ (P.rnDeriv (P+Q) x).toReal := ENNReal.toReal_nonneg
  have hq : 0 ≤ (Q.rnDeriv (P+Q) x).toReal := ENNReal.toReal_nonneg
  simp only [comparisonDensity,add_comm Q P] at hx
  dsimp only [overlapDensity]
  nlinarith [mul_nonneg hp hq,sq_nonneg ((P.rnDeriv (P+Q) x).toReal-(Q.rnDeriv (P+Q) x).toReal)]

theorem integrable_overlapDensity {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q] : Integrable (overlapDensity P Q) (P+Q) :=
  Integrable.of_bound (measurable_overlapDensity P Q).aestronglyMeasurable 1
    ((overlapDensity_le_one P Q).mono (fun x hx => by rw [Real.norm_of_nonneg (overlapDensity_nonneg P Q x)]; exact hx))

theorem affinity_integral_sqrt_overlap {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    (hellingerAffinity P Q).toReal = ∫ x, Real.sqrt (overlapDensity P Q x) ∂(P+Q) := by
  have hm : Measurable (fun x => (P.rnDeriv (P+Q) x*Q.rnDeriv (P+Q) x)^(1/2:ℝ)) := by fun_prop
  have hfin : ∀ᵐ x ∂(P+Q), (P.rnDeriv (P+Q) x*Q.rnDeriv (P+Q) x)^(1/2:ℝ) < ⊤ := by
    filter_upwards [Measure.rnDeriv_lt_top P (P+Q),Measure.rnDeriv_lt_top Q (P+Q)] with x hp hq
    exact lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top hp.ne hq.ne))
  rw [hellingerAffinity,← integral_toReal hm.aemeasurable hfin]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [← ENNReal.toReal_rpow,ENNReal.toReal_mul,Real.sqrt_eq_rpow]
    rfl)

theorem affinity_sq_le_overlap {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (hellingerAffinity P Q).toReal^2 ≤ 2*(∫ x, overlapDensity P Q x ∂(P+Q)) := by
  have hf : MemLp (fun x => Real.sqrt (overlapDensity P Q x)) 2 (P+Q) := by
    apply MemLp.of_bound ((measurable_overlapDensity P Q).sqrt).aestronglyMeasurable 1
    filter_upwards [overlapDensity_le_one P Q] with x hx
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.mpr hx
  have hcs := integral_mul_sq_le (P+Q) hf (memLp_const (1:ℝ))
  have he : (fun x => Real.sqrt (overlapDensity P Q x)^2) = overlapDensity P Q :=
    funext (fun x => Real.sq_sqrt (overlapDensity_nonneg P Q x))
  simp only [mul_one,one_pow,he,integral_const,smul_eq_mul,mul_one] at hcs
  have hm : (P+Q).real Set.univ = 2 := by norm_num [measureReal_def,ENNReal.toReal_add]
  rw [hm,← affinity_integral_sqrt_overlap] at hcs
  nlinarith [hcs]

end ThresholdHC.StoppingProgram
