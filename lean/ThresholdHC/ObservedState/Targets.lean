import Mathlib

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.ObservedState

variable {I : Type} [Fintype I]

/-- The fixed signs of the cells are randomized only for the lower-bound proof. -/
def signLaw (q : I → unitInterval) : Measure (I → Bool) :=
  Measure.pi (fun i => bernoulliMeasure true false (q i))

instance signLaw_probability (q : I → unitInterval) : IsProbabilityMeasure (signLaw q) := by
  unfold signLaw
  infer_instance

def target (w : I → ℝ) (s : I → Bool) : ℝ :=
  ∑ i, w i * (if s i then 1 else 0)

theorem measurable_target (w : I → ℝ) : Measurable (target w) := measurable_of_countable _

theorem bernoulli_value_memLp (q : unitInterval) (w : ℝ) :
    MemLp (fun b : Bool => w * (if b then (1 : ℝ) else 0)) 2 (bernoulliMeasure true false q) := by
  apply MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable |w|
  exact ae_of_all _ (fun b => by cases b <;> simp)

theorem target_memLp (q : I → unitInterval) (w : I → ℝ) :
    MemLp (target w) 2 (signLaw q) :=
  memLp_finsetSum Finset.univ (fun i _ =>
    (bernoulli_value_memLp (q i) (w i)).comp_measurePreserving
      (measurePreserving_eval (fun i => bernoulliMeasure true false (q i)) i))

theorem target_mean (q : I → unitInterval) (w : I → ℝ) :
    (∫ s, target w s ∂signLaw q) = ∑ i, w i * (q i : ℝ) := by
  have hi (i : I) : Integrable (fun s : I → Bool => w i * (if s i then (1 : ℝ) else 0)) (signLaw q) :=
    ((bernoulli_value_memLp (q i) (w i)).comp_measurePreserving
      (measurePreserving_eval (fun i => bernoulliMeasure true false (q i)) i)).integrable (by norm_num)
  unfold target
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_map (μ := signLaw q) (φ := fun s : I → Bool => s i)
    (f := fun b : Bool => w i * (if b then (1 : ℝ) else 0)) (measurable_pi_apply i).aemeasurable
    (measurable_of_countable (fun b : Bool => w i * (if b then (1 : ℝ) else 0))).aestronglyMeasurable]
  rw [signLaw,(measurePreserving_eval (fun i => bernoulliMeasure true false (q i)) i).map_eq,
    integral_bernoulliMeasure]
  simp
  ring

theorem target_variance (q : I → unitInterval) (w : I → ℝ) :
    variance (target w) (signLaw q) = ∑ i, (w i) ^ 2 * (q i : ℝ) * (1 - (q i : ℝ)) := by
  have he : target w = ∑ i, fun s : I → Bool => w i * (if s i then (1 : ℝ) else 0) := by
    funext s
    simp [target]
  rw [he,signLaw,variance_sum_pi (fun i => bernoulli_value_memLp (q i) (w i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [variance_eq_sub (bernoulli_value_memLp (q i) (w i)),
    integral_bernoulliMeasure,integral_bernoulliMeasure]
  norm_num
  ring

theorem target_variance_le (q : I → unitInterval) (w : I → ℝ) :
    variance (target w) (signLaw q) ≤ (∑ i, (w i) ^ 2) / 4 := by
  rw [target_variance,Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  have hq : (q i : ℝ) * (1 - (q i : ℝ)) ≤ 1 / 4 := by
    nlinarith [sq_nonneg ((q i : ℝ) - 1 / 2)]
  nlinarith [mul_le_mul_of_nonneg_left hq (sq_nonneg (w i))]

/-- Replicating cells makes their random target concentrate around its prior mean. -/
theorem target_concentration (q : I → unitInterval) (w : I → ℝ) {r : ℝ} (hr : 0 < r) :
    (signLaw q) {s | r < |target w s - ∑ i, w i * (q i : ℝ)|} ≤
      ENNReal.ofReal ((∑ i, (w i) ^ 2) / (4 * r ^ 2)) := by
  have hc := meas_ge_le_variance_div_sq (target_memLp q w) hr
  rw [target_mean] at hc
  have hm : (signLaw q) {s | r < |target w s - ∑ i, w i * (q i : ℝ)|} ≤
      (signLaw q) {s | r ≤ |target w s - ∑ i, w i * (q i : ℝ)|} :=
    measure_mono (fun s h => show r ≤ |target w s - ∑ i, w i * (q i : ℝ)| from le_of_lt h)
  apply (hm.trans hc).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ((∑ i, (w i) ^ 2) / 4) / r ^ 2 :=
      div_le_div_of_nonneg_right (target_variance_le q w) (sq_nonneg r)
    _ = _ := by ring

end ThresholdHC.ObservedState
