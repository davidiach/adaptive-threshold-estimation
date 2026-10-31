import ThresholdHC.EntropyTailUpper.PoissonMoments
import ThresholdHC.CriticalEntropy.SymmetricReduction

/-! Independent bounded marks sampled a genuine Poisson number of times,
including the zero-count outcome. This module concerns the product sampling
law; its population-policy realization is a separate obligation. -/

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped NNReal BigOperators

namespace ThresholdHC.EntropyTailSampling
open ThresholdHC.EntropyTailUpper ThresholdHC.CriticalEntropy
variable {X : Type} [MeasurableSpace X]

def prefixSum (Y : X → ℝ) (n : ℕ) (x : ℕ → X) : ℝ := ∑ i : Fin n, Y (x i.val)

def countedSum (Y : X → ℝ) (z : ℕ × (ℕ → X)) : ℝ := prefixSum Y z.1 z.2

def markedPoissonLaw (ν : Measure X) (r : ℝ≥0) : Measure (ℕ × (ℕ → X)) :=
  (poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ => ν))

instance markedPoissonLaw_probability (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0) :
    IsProbabilityMeasure (markedPoissonLaw ν r) := by unfold markedPoissonLaw; infer_instance

theorem measurable_prefixSum (Y : X → ℝ) (hY : Measurable Y) (n : ℕ) : Measurable (prefixSum Y n) := by
  apply Finset.measurable_sum
  intro i _
  exact hY.comp (measurable_pi_apply i.val)

theorem measurable_countedSum (Y : X → ℝ) (hY : Measurable Y) : Measurable (countedSum Y) :=
  measurable_from_prod_countable_right (fun n => measurable_prefixSum Y hY n)

omit [MeasurableSpace X] in
theorem prefixSum_norm_le (Y : X → ℝ) {K : ℝ} (hK : ∀ x, ‖Y x‖ ≤ K) (n : ℕ) (x : ℕ → X) :
    ‖prefixSum Y n x‖ ≤ n*K := by
  calc
    _ ≤ ∑ i : Fin n, ‖Y (x i.val)‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin n, K := Finset.sum_le_sum (fun i _ => hK (x i.val))
    _ = _ := by simp

theorem prefix_projection_preserving (ν : Measure X) [IsProbabilityMeasure ν] (n : ℕ) :
    MeasurePreserving (fun x : ℕ → X => fun i : Fin n => x i.val)
      (Measure.infinitePi (fun _ : ℕ => ν)) (Measure.pi (fun _ : Fin n => ν)) := by
  refine ⟨Measurable.of_eval (fun i => measurable_pi_apply i.val), ?_⟩
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]

theorem prefixSum_memLp (ν : Measure X) [IsProbabilityMeasure ν]
    (Y : X → ℝ) (hY : MemLp Y 2 ν) (n : ℕ) :
    MemLp (prefixSum Y n) 2 (Measure.infinitePi (fun _ : ℕ => ν)) :=
  (iid_score_memLp ν Y hY n).comp_measurePreserving (prefix_projection_preserving ν n)

theorem prefixSum_mean (ν : Measure X) [IsProbabilityMeasure ν]
    (Y : X → ℝ) (hYm : Measurable Y) (hY : MemLp Y 2 ν) (n : ℕ) :
    (∫ x, prefixSum Y n x ∂Measure.infinitePi (fun _ : ℕ => ν)) = n*(∫ x, Y x ∂ν) := by
  have hm : Measurable (fun x : Fin n → X => ∑ i, Y (x i)) :=
    Finset.measurable_sum _ (fun i _ => hYm.comp (measurable_pi_apply i))
  change (∫ x : ℕ → X, (fun y : Fin n → X => ∑ i, Y (y i)) (fun i => x i.val) ∂_) = _
  rw [← integral_map (prefix_projection_preserving ν n).measurable.aemeasurable hm.aestronglyMeasurable,
    (prefix_projection_preserving ν n).map_eq]
  exact iid_score_integral ν Y hY n

theorem prefixSum_second (ν : Measure X) [IsProbabilityMeasure ν]
    (Y : X → ℝ) (hYm : Measurable Y) (hY : MemLp Y 2 ν) (n : ℕ) :
    (∫ x, (prefixSum Y n x)^2 ∂Measure.infinitePi (fun _ : ℕ => ν)) =
      n*(∫ x, (Y x)^2 ∂ν)+((n:ℝ)^2-n)*(∫ x, Y x ∂ν)^2 := by
  have hm : Measurable (fun x : Fin n → X => (∑ i, Y (x i))^2) :=
    (Finset.measurable_sum _ (fun i _ => hYm.comp (measurable_pi_apply i))).pow_const 2
  change (∫ x : ℕ → X, (fun y : Fin n → X => (∑ i, Y (y i))^2) (fun i => x i.val) ∂_) = _
  rw [← integral_map (prefix_projection_preserving ν n).measurable.aemeasurable hm.aestronglyMeasurable,
    (prefix_projection_preserving ν n).map_eq]
  have h := variance_eq_sub (iid_score_memLp ν Y hY n)
  rw [iid_score_variance ν Y hY n, iid_score_integral ν Y hY n, variance_eq_sub hY] at h
  dsimp only [Pi.pow_apply] at h
  nlinarith only [h]

theorem countedSum_integrable (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    (Y : X → ℝ) (hYm : Measurable Y) {K : ℝ} (hK : ∀ x, ‖Y x‖ ≤ K) :
    Integrable (countedSum Y) (markedPoissonLaw ν r) := by
  have hi : Integrable (fun z : ℕ × (ℕ → X) => (z.1:ℝ)) (markedPoissonLaw ν r) :=
    measurePreserving_fst.integrable_comp_of_integrable (poisson_count_integrable r)
  apply (hi.mul_const K).mono' (measurable_countedSum Y hYm).aestronglyMeasurable
  exact ae_of_all _ (fun z => prefixSum_norm_le Y hK z.1 z.2)

theorem countedSum_sq_integrable (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    (Y : X → ℝ) (hYm : Measurable Y) {K : ℝ} (_hK0 : 0 ≤ K) (hK : ∀ x, ‖Y x‖ ≤ K) :
    Integrable (fun z => (countedSum Y z)^2) (markedPoissonLaw ν r) := by
  have hi : Integrable (fun z : ℕ × (ℕ → X) => (z.1:ℝ)^2) (markedPoissonLaw ν r) :=
    measurePreserving_fst.integrable_comp_of_integrable (poisson_count_sq_integrable r)
  apply (hi.mul_const (K^2)).mono' ((measurable_countedSum Y hYm).pow_const 2).aestronglyMeasurable
  apply ae_of_all
  intro z
  have h := pow_le_pow_left₀ (norm_nonneg (prefixSum Y z.1 z.2)) (prefixSum_norm_le Y hK z.1 z.2) 2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [countedSum, Real.norm_eq_abs, sq_abs, mul_pow] using h

theorem countedSum_memLp (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    (Y : X → ℝ) (hYm : Measurable Y) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ x, ‖Y x‖ ≤ K) :
    MemLp (countedSum Y) 2 (markedPoissonLaw ν r) :=
  (memLp_two_iff_integrable_sq (measurable_countedSum Y hYm).aestronglyMeasurable).mpr
    (countedSum_sq_integrable ν r Y hYm hK0 hK)

theorem countedSum_mean (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    (Y : X → ℝ) (hYm : Measurable Y) (hY : MemLp Y 2 ν) {K : ℝ} (hK : ∀ x, ‖Y x‖ ≤ K) :
    (∫ z, countedSum Y z ∂markedPoissonLaw ν r) = (r:ℝ)*(∫ x, Y x ∂ν) := by
  rw [markedPoissonLaw, integral_prod _ (countedSum_integrable ν r Y hYm hK)]
  simp only [countedSum, prefixSum_mean ν Y hYm hY]
  rw [integral_mul_const, poisson_count_mean]

theorem countedSum_second (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    (Y : X → ℝ) (hYm : Measurable Y) (hY : MemLp Y 2 ν)
    {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ x, ‖Y x‖ ≤ K) :
    (∫ z, (countedSum Y z)^2 ∂markedPoissonLaw ν r) =
      (r:ℝ)*(∫ x, (Y x)^2 ∂ν)+(r:ℝ)^2*(∫ x, Y x ∂ν)^2 := by
  rw [markedPoissonLaw, integral_prod _ (countedSum_sq_integrable ν r Y hYm hK0 hK)]
  simp only [countedSum, prefixSum_second ν Y hYm hY]
  have ha := integral_add ((poisson_count_integrable r).mul_const (∫ x, (Y x)^2 ∂ν))
    (((poisson_count_sq_integrable r).sub (poisson_count_integrable r)).mul_const ((∫ x, Y x ∂ν)^2))
  have hs := integral_sub (poisson_count_sq_integrable r) (poisson_count_integrable r)
  dsimp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply] at ha hs
  rw [ha, integral_mul_const, integral_mul_const, hs, poisson_count_mean, poisson_count_second_moment]
  ring

end ThresholdHC.EntropyTailSampling
