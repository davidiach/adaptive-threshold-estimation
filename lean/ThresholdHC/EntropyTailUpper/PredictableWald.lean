import ThresholdHC.EntropyTailUpper.BoundedSearch
import Mathlib.Probability.Independence.Integration

/-! A finite Wald identity for observable stopping counts. Only bounded
stopping is used; unbounded expected work is not assumed in the proof. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace ThresholdHC.EntropyTailUpper
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy

theorem prefix_indep_next (p : unitInterval) (n : ℕ) :
    IndepFun (tapePrefix n) (fun ω : ℕ → Bool => ω n) (tapeMeasure p) := by
  have hi : iIndepFun (fun i (ω : ℕ → Bool) => ω i) (tapeMeasure p) :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have h := hi.indepFun_set (Iio n) {n} (by
    apply Set.disjoint_left.mpr
    intro i hi hj
    simp only [mem_Iio, mem_singleton_iff] at hi hj
    omega) (fun i => measurable_pi_apply i)
  exact h.comp
    (show Measurable (fun w : Iio n → Bool => fun i : Fin n => w ⟨i.val, i.isLt⟩) by fun_prop)
    (measurable_pi_apply (⟨n, by simp⟩ : ({n} : Set ℕ)))

def bitScoreMean (p : unitInterval) (f : Bool → ℝ) : ℝ :=
  (p:ℝ)*f true + (1-(p:ℝ))*f false

theorem integral_bitScore (p : unitInterval) (f : Bool → ℝ) (n : ℕ) :
    (∫ ω, f (ω n) ∂tapeMeasure p) = bitScoreMean p f := by
  have h := measurePreserving_eval_infinitePi
    (fun _ : ℕ => bernoulliMeasure true false p) n
  change (∫ ω : ℕ → Bool, f (ω n) ∂Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false p)) = _
  rw [← integral_map (measurable_pi_apply n).aemeasurable (measurable_of_countable f).aestronglyMeasurable,
    h.map_eq, integral_bernoulliMeasure]
  rfl

theorem stopped_by_prefix {τ : (ℕ → Bool) → ℕ}
    (hext : ∀ ω ω', tapePrefix (τ ω) ω = tapePrefix (τ ω) ω' → τ ω' = τ ω)
    (n : ℕ) {ω ω' : ℕ → Bool} (he : tapePrefix n ω = tapePrefix n ω') :
    τ ω ≤ n ↔ τ ω' ≤ n := by
  constructor
  · intro h
    rw [hext ω ω' (prefix_eq_restrict he h)]
    exact h
  · intro h
    rw [hext ω' ω (prefix_eq_restrict he.symm h)]
    exact h

def survives (τ : (ℕ → Bool) → ℕ) (n : ℕ) (ω : ℕ → Bool) : ℝ :=
  if n < τ ω then 1 else 0

theorem survives_prefix {τ : (ℕ → Bool) → ℕ}
    (hext : ∀ ω ω', tapePrefix (τ ω) ω = tapePrefix (τ ω) ω' → τ ω' = τ ω)
    (n : ℕ) : survives τ n = (fun w => survives τ n (completePrefix n w)) ∘ tapePrefix n := by
  funext ω
  have h := stopped_by_prefix hext n (tapePrefix_completePrefix n (tapePrefix n ω)).symm
  simp only [survives, Function.comp_apply, ← not_le, h]

theorem measurable_survives {τ : (ℕ → Bool) → ℕ}
    (hext : ∀ ω ω', tapePrefix (τ ω) ω = tapePrefix (τ ω) ω' → τ ω' = τ ω)
    (n : ℕ) : Measurable (survives τ n) := by
  rw [survives_prefix hext]
  exact (measurable_of_countable _).comp (measurable_prefix n)

theorem integrable_survives (p : unitInterval) {τ : (ℕ → Bool) → ℕ}
    (hext : ∀ ω ω', tapePrefix (τ ω) ω = tapePrefix (τ ω) ω' → τ ω' = τ ω)
    (n : ℕ) : Integrable (survives τ n) (tapeMeasure p) := by
  apply Integrable.of_bound (measurable_survives hext n).aestronglyMeasurable 1
  exact ae_of_all _ (fun ω => by unfold survives; split_ifs <;> norm_num)

theorem integrable_survives_score (p : unitInterval) (f : Bool → ℝ) {τ : (ℕ → Bool) → ℕ}
    (hext : ∀ ω ω', tapePrefix (τ ω) ω = tapePrefix (τ ω) ω' → τ ω' = τ ω)
    (n : ℕ) : Integrable (fun ω => survives τ n ω * f (ω n)) (tapeMeasure p) := by
  apply Integrable.of_bound
    ((measurable_survives hext n).mul ((measurable_of_countable f).comp (measurable_pi_apply n))).aestronglyMeasurable
    (|f true|+|f false|)
  refine ae_of_all _ (fun ω => ?_)
  change ‖survives τ n ω * f (ω n)‖ ≤ |f true|+|f false|
  unfold survives
  split_ifs
  · cases ω n <;> simp only [one_mul, Real.norm_eq_abs] <;>
      linarith [abs_nonneg (f true), abs_nonneg (f false)]
  · simp only [zero_mul, norm_zero]; positivity

theorem integral_survives_score (p : unitInterval) (f : Bool → ℝ) {τ : (ℕ → Bool) → ℕ}
    (hext : ∀ ω ω', tapePrefix (τ ω) ω = tapePrefix (τ ω) ω' → τ ω' = τ ω)
    (n : ℕ) :
    (∫ ω, survives τ n ω * f (ω n) ∂tapeMeasure p) =
      (∫ ω, survives τ n ω ∂tapeMeasure p) * bitScoreMean p f := by
  have hi : IndepFun (survives τ n) (fun ω : ℕ → Bool => f (ω n)) (tapeMeasure p) := by
    rw [survives_prefix hext]
    exact (prefix_indep_next p n).comp (measurable_of_countable _) (measurable_of_countable f)
  rw [hi.integral_fun_mul_eq_mul_integral (measurable_survives hext n).aestronglyMeasurable
    (((measurable_of_countable f).comp (measurable_pi_apply n)).aestronglyMeasurable), integral_bitScore]

theorem stopped_sum_eq (f : Bool → ℝ) (τ : (ℕ → Bool) → ℕ) (M : ℕ)
    (hM : ∀ ω, τ ω ≤ M) (ω : ℕ → Bool) :
    (∑ i ∈ Finset.range (τ ω), f (ω i)) =
      ∑ i ∈ Finset.range M, survives τ i ω * f (ω i) := by
  classical
  calc
    _ = ∑ i ∈ Finset.range (τ ω), survives τ i ω * f (ω i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [survives, Finset.mem_range.mp hi]
    _ = _ := Finset.sum_subset (Finset.range_mono (hM ω)) (fun i _ hi => by
      simp only [Finset.mem_range, not_lt] at hi
      simp [survives, not_lt.mpr hi])

theorem stopped_count_eq (τ : (ℕ → Bool) → ℕ) (M : ℕ)
    (hM : ∀ ω, τ ω ≤ M) (ω : ℕ → Bool) :
    (τ ω : ℝ) = ∑ i ∈ Finset.range M, survives τ i ω := by
  simpa using stopped_sum_eq (fun _ => (1:ℝ)) τ M hM ω

theorem bounded_wald (p : unitInterval) (f : Bool → ℝ) (τ : (ℕ → Bool) → ℕ) (M : ℕ)
    (hM : ∀ ω, τ ω ≤ M)
    (hext : ∀ ω ω', tapePrefix (τ ω) ω = tapePrefix (τ ω) ω' → τ ω' = τ ω) :
    (∫ ω, (∑ i ∈ Finset.range (τ ω), f (ω i)) ∂tapeMeasure p) =
      (∫ ω, (τ ω : ℝ) ∂tapeMeasure p) * bitScoreMean p f := by
  simp_rw [stopped_sum_eq f τ M hM, stopped_count_eq τ M hM]
  rw [integral_finsetSum _ (fun i _ => integrable_survives_score p f hext i),
    integral_finsetSum _ (fun i _ => integrable_survives p hext i), Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => integral_survives_score p f hext i)

end ThresholdHC.EntropyTailUpper
