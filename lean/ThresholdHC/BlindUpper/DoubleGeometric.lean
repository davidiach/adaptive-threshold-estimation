import ThresholdHC.Proofs.Calibration
import Mathlib.Probability.Distributions.Geometric

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Failures in two independent first-success pilot streams. -/
def doubleFailuresLaw (p : unitInterval) : Measure ℕ :=
  ((geometricMeasure p).prod (geometricMeasure p)).map (fun z => z.1+z.2)

instance doubleFailuresLaw_probability (p : unitInterval) : IsProbabilityMeasure (doubleFailuresLaw p) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_of_countable (fun z : ℕ × ℕ => z.1+z.2)).aemeasurable).2 inferInstance

theorem doubleFailures_singleton (p : unitInterval) (hp : p ≠ 0) (k : ℕ) :
    doubleFailuresLaw p {k} = ENNReal.ofReal (((k : ℝ)+1)*(p : ℝ)^2*(1-(p : ℝ))^k) := by
  have hm : Measurable (fun z : ℕ × ℕ => z.1+z.2) := measurable_of_countable _
  rw [doubleFailuresLaw,Measure.map_apply hm (measurableSet_singleton k),
    Measure.prod_apply (hm (measurableSet_singleton k)),lintegral_countable']
  have hf (i : ℕ) :
      geometricMeasure p (Prod.mk i ⁻¹' ((fun z : ℕ × ℕ => z.1+z.2) ⁻¹' {k})) =
      if i ≤ k then geometricMeasure p {k-i} else 0 := by
    by_cases hi : i ≤ k
    · rw [ite_eq_left hi]
      congr 1
      ext j
      simp only [Set.mem_preimage,Set.mem_singleton_iff]
      omega
    · rw [ite_eq_right hi]
      have he : Prod.mk i ⁻¹' ((fun z : ℕ × ℕ => z.1+z.2) ⁻¹' {k}) = ∅ := by
        ext j
        simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_empty_iff_false,iff_false]
        omega
      rw [he,measure_empty]
  simp_rw [hf]
  rw [tsum_eq_sum (s := Finset.range (k+1)) (fun i hi => by
    have hik : ¬i ≤ k := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi
    simp [hik])]
  have hterm (i : ℕ) (hi : i ∈ Finset.range (k+1)) :
      (if i ≤ k then geometricMeasure p {k-i} else 0)*geometricMeasure p {i} =
        ENNReal.ofReal ((p : ℝ)^2*(1-(p : ℝ))^k) := by
    have hik : i ≤ k := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi
    rw [ite_eq_left hik,geometricMeasure_singleton hp,geometricMeasure_singleton hp,
      ← ENNReal.ofReal_mul (geometricMeasure_nonneg p (k-i))]
    congr 1
    calc
      _ = (1-(p : ℝ))^(k-i+i)*(p : ℝ)^2 := by rw [pow_add]; ring
      _ = _ := by rw [Nat.sub_add_cancel hik]; ring
  rw [Finset.sum_congr rfl hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi =>
    mul_nonneg (sq_nonneg _) (pow_nonneg (sub_nonneg.mpr p.property.2) k))]
  congr 1
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  ring

theorem doubleFailures_real_singleton (p : unitInterval) (hp : p ≠ 0) (k : ℕ) :
    (doubleFailuresLaw p).real {k} = ((k : ℝ)+1)*(p : ℝ)^2*(1-(p : ℝ))^k := by
  rw [measureReal_def,doubleFailures_singleton p hp,ENNReal.toReal_ofReal]
  exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
    (pow_nonneg (sub_nonneg.mpr p.property.2) _)


theorem discrete_integrable_of_summable (ν : Measure ℕ) [IsFiniteMeasure ν]
    (f : ℕ → ℝ) (h : Summable (fun n => ν.real {n} * ‖f n‖)) : Integrable f ν := by
  rw [← Measure.sum_smul_dirac ν]
  apply integrable_sum_dirac (fun n => measure_ne_top ν {n})
  exact h

theorem doubleFailures_count_integrable (p : unitInterval) (hp : 0 < (p : ℝ)) :
    Integrable (fun n : ℕ => (n : ℝ)+2) (doubleFailuresLaw p) := by
  have hp' : p ≠ 0 := by intro h; simpa [h] using hp
  have hs : Summable (fun n : ℕ => ((n : ℝ)+2)*(((n : ℝ)+1)*(p : ℝ)^2*(1-(p : ℝ))^n)) :=
    by
      by_contra h
      have hz := tsum_eq_zero_of_not_summable h
      rw [Proofs.negbin_mean p hp p.property.2] at hz
      exact (ne_of_gt (div_pos (by norm_num : (0 : ℝ) < 2) hp)) hz
  apply discrete_integrable_of_summable
  convert hs using 1
  funext n
  rw [doubleFailures_real_singleton p hp',Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  ring

theorem doubleFailures_count_mean (p : unitInterval) (hp : 0 < (p : ℝ)) :
    (∫ n, (n : ℝ)+2 ∂doubleFailuresLaw p) = 2/(p : ℝ) := by
  have hp' : p ≠ 0 := by intro h; simpa [h] using hp
  rw [integral_countable (doubleFailures_count_integrable p hp)]
  simp_rw [doubleFailures_real_singleton p hp',smul_eq_mul]
  convert Proofs.negbin_mean p hp p.property.2 using 1
  congr 1
  funext n
  ring

theorem doubleFailures_inverse_integrable (p : unitInterval) :
    Integrable (fun n : ℕ => ((n : ℝ)+1)⁻¹) (doubleFailuresLaw p) := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  exact ae_of_all _ (fun n => by
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact (inv_le_one₀ (by positivity)).mpr (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith))

theorem doubleFailures_inverse_mean (p : unitInterval) (hp : 0 < (p : ℝ)) :
    (∫ n, ((n : ℝ)+1)⁻¹ ∂doubleFailuresLaw p) = (p : ℝ) := by
  have hp' : p ≠ 0 := by intro h; simpa [h] using hp
  rw [integral_countable (doubleFailures_inverse_integrable p)]
  simp_rw [doubleFailures_real_singleton p hp',smul_eq_mul]
  convert Proofs.haldane_inverse_moment p hp p.property.2 using 1
  congr 1
  funext n
  ring


end ThresholdHC.BlindUpper
