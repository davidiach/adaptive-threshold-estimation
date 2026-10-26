import ThresholdHC.Statements2
import ThresholdHC.Uniform713.Concentration
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

noncomputable section
open MeasureTheory ProbabilityTheory Real

namespace ThresholdHC.Tier2

def bit (b : Bool) : ℝ := if b then 1 else 0
def tapeMeasure (p : unitInterval) : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false p)
def finiteMeasure (p : unitInterval) (M : ℕ) : Measure (Fin M → Bool) :=
  Measure.pi (fun _ : Fin M => bernoulliMeasure true false p)
def tapePrefix (M : ℕ) (ω : ℕ → Bool) : Fin M → Bool := fun i => ω i.val
def observations (i : ℕ) (ω : ℕ → Bool) : ℝ := bit (ω i)

instance (p : unitInterval) : IsProbabilityMeasure (tapeMeasure p) := by
  unfold tapeMeasure
  infer_instance
instance (p : unitInterval) (M : ℕ) : IsProbabilityMeasure (finiteMeasure p M) := by
  unfold finiteMeasure
  infer_instance

theorem measurable_bit : Measurable bit := measurable_of_countable _
theorem measurable_observations (i : ℕ) : Measurable (observations i) :=
  measurable_bit.comp (measurable_pi_apply i)
theorem measurable_prefix (M : ℕ) : Measurable (tapePrefix M) := by
  exact Measurable.of_eval (fun i : Fin M => measurable_pi_apply i.val)

theorem observations_mean (p : unitInterval) (i : ℕ) :
    ∫ ω, observations i ω ∂tapeMeasure p = (p : ℝ) := by
  have h := measurePreserving_eval_infinitePi
    (fun _ : ℕ => bernoulliMeasure true false p) i
  change ∫ ω, bit (ω i) ∂Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false p) = _
  rw [← integral_map (measurable_pi_apply i).aemeasurable measurable_bit.aestronglyMeasurable, h.map_eq]
  rw [integral_bernoulliMeasure]
  simp [bit]

theorem observations_independent (p : unitInterval) :
    iIndepFun observations (tapeMeasure p) := by
  exact iIndepFun_infinitePi (X := fun _ => bit) (fun _ => measurable_bit)

theorem tape_mean_tails (p : unitInterval) :
    Uniform713.HasMeanTails (tapeMeasure p) (Uniform713.dyadicMean observations) (p : ℝ) := by
  apply Uniform713.hasMeanTails_of_independent_bounded measurable_observations
  · intro i
    filter_upwards [] with ω
    simp only [observations, bit]
    split <;> norm_num
  · exact observations_mean p
  · exact observations_independent p

theorem prefix_map (p : unitInterval) (M : ℕ) :
    (tapeMeasure p).map (tapePrefix M) = finiteMeasure p M := by
  unfold tapeMeasure tapePrefix finiteMeasure
  rw [Measure.map_infinitePi_infinitePi_of_inj (Fin.val_injective), Measure.infinitePi_eq_pi]

theorem bernoulli_real_singleton (p : unitInterval) (b : Bool) :
    (bernoulliMeasure true false p).real {b} = if b then (p : ℝ) else 1 - (p : ℝ) := by
  cases b
  · exact bernoulliMeasure_real_apply_of_notMem_of_mem p (measurableSet_singleton false)
      (by simp) (by simp)
  · exact bernoulliMeasure_real_apply_of_mem_of_notMem p (measurableSet_singleton true)
      (by simp) (by simp)

theorem finiteMeasure_real_singleton (p : unitInterval) {M : ℕ} (x : Fin M → Bool) :
    (finiteMeasure p M).real {x} = streamProb (p : ℝ) x := by
  simp only [Measure.real, finiteMeasure, Measure.pi_singleton, ENNReal.toReal_prod,
    streamProb]
  apply Finset.prod_congr rfl
  intro i hi
  exact bernoulli_real_singleton p (x i)

theorem finite_integrable (p : unitInterval) {M : ℕ} (f : (Fin M → Bool) → ℝ) :
    Integrable f (finiteMeasure p M) := by
  apply Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable
    (∑ x, ‖f x‖)
  filter_upwards [] with x
  exact Finset.single_le_sum (fun y _ => norm_nonneg (f y)) (Finset.mem_univ x)

theorem integral_finiteMeasure (p : unitInterval) {M : ℕ} (f : (Fin M → Bool) → ℝ) :
    ∫ x, f x ∂finiteMeasure p M = ∑ x, streamProb (p : ℝ) x * f x := by
  rw [integral_fintype (finite_integrable p f)]
  simp only [finiteMeasure_real_singleton, smul_eq_mul]

theorem integral_prefix (p : unitInterval) {M : ℕ} (f : (Fin M → Bool) → ℝ) :
    ∫ ω, f (tapePrefix M ω) ∂tapeMeasure p = ∑ x, streamProb (p : ℝ) x * f x := by
  rw [← integral_finiteMeasure]
  have h : MeasurePreserving (tapePrefix M) (tapeMeasure p) (finiteMeasure p M) :=
    ⟨measurable_prefix M, prefix_map p M⟩
  rw [← h.map_eq]
  exact (integral_map h.measurable.aemeasurable (measurable_of_countable f).aestronglyMeasurable).symm

end ThresholdHC.Tier2


