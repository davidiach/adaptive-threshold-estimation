import ThresholdHC.CriticalEntropy.SampleMean

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem iid_score_memLp {I : Type} [MeasurableSpace I]
    (μ : Measure I) [IsProbabilityMeasure μ] (u : I → ℝ) (h : MemLp u 2 μ) (n : ℕ) :
    MemLp (fun x : Fin n → I => ∑ i, u (x i)) 2 (Measure.pi (fun _ : Fin n => μ)) := by
  exact memLp_finsetSum Finset.univ (fun i _ =>
    h.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) i))

theorem iid_score_integral {I : Type} [MeasurableSpace I]
    (μ : Measure I) [IsProbabilityMeasure μ] (u : I → ℝ) (h : MemLp u 2 μ) (n : ℕ) :
    (∫ x : Fin n → I, ∑ i, u (x i) ∂Measure.pi (fun _ : Fin n => μ)) =
      (n : ℝ)*(∫ x, u x ∂μ) := by
  have hi (i : Fin n) : Integrable (fun x : Fin n → I => u (x i))
      (Measure.pi (fun _ : Fin n => μ)) :=
    (h.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) i)).integrable (by norm_num)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  have he (i : Fin n) :
      (∫ x : Fin n → I, u (x i) ∂Measure.pi (fun _ : Fin n => μ)) = ∫ x, u x ∂μ := by
    have hm := (measurePreserving_eval (fun _ : Fin n => μ) i).map_eq
    calc
      _ = ∫ x, u x ∂(Measure.pi (fun _ : Fin n => μ)).map (fun x => x i) :=
        (integral_map (measurable_pi_apply i).aemeasurable (by rw [hm]; exact h.aestronglyMeasurable)).symm
      _ = _ := by rw [hm]
  simp_rw [he]
  simp

theorem iid_score_variance {I : Type} [MeasurableSpace I]
    (μ : Measure I) [IsProbabilityMeasure μ] (u : I → ℝ) (h : MemLp u 2 μ) (n : ℕ) :
    variance (fun x : Fin n → I => ∑ i, u (x i)) (Measure.pi (fun _ : Fin n => μ)) =
      (n : ℝ)*variance u μ := by
  have hh := variance_sum_pi (μ := fun _ : Fin n => μ) (X := fun _ => u) (fun _ => h)
  calc
    _ = variance (∑ i : Fin n, fun x : Fin n → I => u (x i))
      (Measure.pi (fun _ : Fin n => μ)) := by congr 1; ext x; simp
    _ = ∑ _ : Fin n, variance u μ := hh
    _ = _ := by simp

theorem symmetric_one_run_reduction {I : Type} [MeasurableSpace I]
    (μ : Measure I) [IsProbabilityMeasure μ] (u : I → ℝ)
    (h : MemLp u 2 μ) (n : ℕ) (c θ V : ℝ)
    (hM : (∫ x : Fin n → I, (c+(∑ i, u (x i))-θ)^2 ∂Measure.pi (fun _ : Fin n => μ)) ≤ V) :
    ((∫ x, (n : ℝ)*u x+c ∂μ)-θ)^2 ≤ V ∧
    evariance (fun x => (n : ℝ)*u x+c) μ ≤ ENNReal.ofReal ((n : ℝ)*V) := by
  let ν := Measure.pi (fun _ : Fin n => μ)
  let S : (Fin n → I) → ℝ := fun x => ∑ i, u (x i)
  have hS : MemLp S 2 ν := iid_score_memLp μ u h n
  have hE : MemLp (fun x : Fin n → I => c+S x-θ) 2 ν :=
    ((memLp_const c).add hS).sub (memLp_const θ)
  have hZ : MemLp (fun x => (n : ℝ)*u x+c) 2 μ :=
    (h.const_mul (n : ℝ)).add (memLp_const c)
  have hmE : (∫ x : Fin n → I, c+S x-θ ∂ν) = c+(n : ℝ)*(∫ x, u x ∂μ)-θ := by
    have hi : Integrable (fun x => c+S x) ν := (integrable_const c).add (hS.integrable (by norm_num))
    rw [integral_sub hi (integrable_const θ),
      integral_add (integrable_const c) (hS.integrable (by norm_num))]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    rw [iid_score_integral μ u h n]
  have hmZ : (∫ x, (n : ℝ)*u x+c ∂μ) = (n : ℝ)*(∫ x, u x ∂μ)+c := by
    have hi : Integrable (fun x => (n : ℝ)*u x) μ := (h.integrable (by norm_num)).const_mul (n : ℝ)
    rw [integral_add hi (integrable_const c),
      integral_const_mul]
    simp
  have hvar : variance (fun x => c+S x-θ) ν = (n : ℝ)*variance u μ := by
    have hcs : AEStronglyMeasurable (fun x => c+S x) ν :=
      aestronglyMeasurable_const.add hS.aestronglyMeasurable
    rw [variance_sub_const hcs,variance_const_add hS.aestronglyMeasurable,
      iid_score_variance μ u h n]
  constructor
  · have hv := variance_nonneg (fun x : Fin n → I => c+S x-θ) ν
    rw [variance_eq_sub hE,hmE] at hv
    simp only [Pi.pow_apply] at hv
    rw [hmZ]
    change (∫ x : Fin n → I, (c+S x-θ)^2 ∂ν) ≤ V at hM
    nlinarith
  · rw [← ofReal_variance hZ,variance_add_const (h.const_mul (n : ℝ)).aestronglyMeasurable,variance_const_mul]
    apply ENNReal.ofReal_le_ofReal
    have hv := (variance_le_expectation_sq hE.aestronglyMeasurable).trans hM
    rw [hvar] at hv
    have hmult := mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    change (n : ℝ)^2*variance u μ ≤ (n : ℝ)*V
    simpa only [pow_two,mul_assoc] using hmult

end ThresholdHC.CriticalEntropy
