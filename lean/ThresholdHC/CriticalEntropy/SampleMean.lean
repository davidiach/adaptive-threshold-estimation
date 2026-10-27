import Mathlib

/-!
Second-moment bounds for iid real outputs. Chebyshev is applied to the actual
finite product measure, with its expectation and variance identities proved.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem iid_sum_memLp (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : MemLp id 2 μ) (n : ℕ) :
    MemLp (fun x : Fin n → ℝ => ∑ i, x i) 2 (Measure.pi (fun _ : Fin n => μ)) := by
  have hi (i : Fin n) : MemLp (fun x : Fin n → ℝ => x i) 2
      (Measure.pi (fun _ : Fin n => μ)) :=
    h.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) i)
  exact memLp_finsetSum Finset.univ (fun i _ => hi i)

theorem iid_sum_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : MemLp id 2 μ) (n : ℕ) :
    (∫ x : Fin n → ℝ, ∑ i, x i ∂Measure.pi (fun _ : Fin n => μ)) =
      (n : ℝ) * ∫ x, x ∂μ := by
  have hi (i : Fin n) : Integrable (fun x : Fin n → ℝ => x i)
      (Measure.pi (fun _ : Fin n => μ)) :=
    (h.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) i)).integrable
      (by norm_num)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  have he (i : Fin n) :
      (∫ x : Fin n → ℝ, x i ∂Measure.pi (fun _ : Fin n => μ)) = ∫ x, x ∂μ := by
    have hm := (measurePreserving_eval (fun _ : Fin n => μ) i).map_eq
    calc
      _ = ∫ x : ℝ, x ∂(Measure.pi (fun _ : Fin n => μ)).map (fun x => x i) :=
        (integral_map (μ := Measure.pi (fun _ : Fin n => μ))
          (φ := fun x : Fin n → ℝ => x i) (f := fun x : ℝ => x)
          (measurable_pi_apply i).aemeasurable
          measurable_id.aestronglyMeasurable).symm
      _ = _ := by rw [hm]
  simp_rw [he]
  simp

theorem iid_sum_variance (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : MemLp id 2 μ) (n : ℕ) :
    variance (fun x : Fin n → ℝ => ∑ i, x i) (Measure.pi (fun _ : Fin n => μ)) =
      (n : ℝ) * variance id μ := by
  have hh := variance_sum_pi (μ := fun _ : Fin n => μ) (X := fun _ => id) (fun _ => h)
  calc
    _ = variance (∑ i : Fin n, fun x : Fin n → ℝ => id (x i))
        (Measure.pi (fun _ : Fin n => μ)) := by congr 1; ext x; simp
    _ = ∑ _ : Fin n, variance id μ := hh
    _ = _ := by simp

theorem iid_sum_deviation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : MemLp id 2 μ) (n : ℕ) (hn : 0 < n) (a M : ℝ) (ha : 0 < a)
    (hM : (∫ x : ℝ, x^2 ∂μ) ≤ M) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {x | (n : ℝ)*a ≤ |(∑ i, x i) - (n : ℝ)*(∫ y, y ∂μ)|} ≤
      M / ((n : ℝ)*a^2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc := meas_ge_le_variance_div_sq (iid_sum_memLp μ h n) (mul_pos hn' ha)
  rw [iid_sum_integral μ h n, iid_sum_variance μ h n] at hc
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
  have hv0 : 0 ≤ variance id μ := variance_nonneg _ _
  rw [ENNReal.toReal_ofReal (by positivity)] at hr
  change (Measure.pi (fun _ : Fin n => μ)).real _ ≤ _ at hr
  have hv : variance id μ ≤ M := by
    exact (variance_le_expectation_sq measurable_id.aestronglyMeasurable).trans hM
  calc
    _ ≤ (n : ℝ)*variance id μ / ((n : ℝ)*a)^2 := hr
    _ ≤ (n : ℝ)*M / ((n : ℝ)*a)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv hn'.le) (sq_nonneg _)
    _ = _ := by field_simp

theorem iid_sum_lower_error (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : MemLp id 2 μ) (n : ℕ) (hn : 0 < n) (a M t : ℝ) (ha : 0 < a)
    (hM : (∫ x : ℝ, x^2 ∂μ) ≤ M) (hm : t+a ≤ ∫ x, x ∂μ) :
    (Measure.pi (fun _ : Fin n => μ)).real {x | (∑ i, x i) ≤ (n : ℝ)*t} ≤
      M / ((n : ℝ)*a^2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply le_trans (measureReal_mono ?_) (iid_sum_deviation μ h n hn a M ha hM)
  intro x hx
  change (n : ℝ)*a ≤ |(∑ i, x i) - (n : ℝ)*(∫ y, y ∂μ)|
  have hmul := mul_le_mul_of_nonneg_left hm hn'.le
  have habs := neg_le_abs ((∑ i, x i) - (n : ℝ)*(∫ y, y ∂μ))
  change (∑ i, x i) ≤ (n : ℝ)*t at hx
  nlinarith

theorem iid_sum_upper_error (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : MemLp id 2 μ) (n : ℕ) (hn : 0 < n) (a M t : ℝ) (ha : 0 < a)
    (hM : (∫ x : ℝ, x^2 ∂μ) ≤ M) (hm : (∫ x, x ∂μ)+a ≤ t) :
    (Measure.pi (fun _ : Fin n => μ)).real {x | (n : ℝ)*t < (∑ i, x i)} ≤
      M / ((n : ℝ)*a^2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply le_trans (measureReal_mono ?_) (iid_sum_deviation μ h n hn a M ha hM)
  intro x hx
  change (n : ℝ)*a ≤ |(∑ i, x i) - (n : ℝ)*(∫ y, y ∂μ)|
  have hmul := mul_le_mul_of_nonneg_left hm hn'.le
  have habs := le_abs_self ((∑ i, x i) - (n : ℝ)*(∫ y, y ∂μ))
  change (n : ℝ)*t < (∑ i, x i) at hx
  nlinarith

end ThresholdHC.CriticalEntropy
