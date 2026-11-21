import ThresholdHC.FiniteBayesAllocation.Weight
import ThresholdHC.CriticalEntropy.ObservablePopulation
import ThresholdHC.Tier6.Full
import ThresholdHC.RareAboveTwo.TerminalInformation
import ThresholdHC.HardBudget.Controller

/-! The mean squared error of the original experiment as a seed average of a
finite sum over the observed words of length `n` (the horizon-`n` form of
`TwoFlipFeedback/Risk.lean`). An estimator whose output reads only the first
`n` observations has exactly that risk; for a target `θ` in `[0, M]`, an
estimator under a pathwise cap of `n` flips has at least the risk of its output
clipped to `[0, M]` and read from the padded `n`-prefix. -/

noncomputable section
namespace ThresholdHC.FiniteBayesAllocation
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open ThresholdHC.HardBudget

/-- The gap as a real number. -/
abbrev gapReal : Gap → ℝ := fun d => (d : ℝ)

/-- Observable horizon-`n` weight of seed `r` after integrating the hidden
magnitudes and signs. -/
def seedWeight {R : Type} [MeasurableSpace R] (μ : Measure Gap) (A : AdaptiveEstimator R)
    (q : SignLaw) {n : ℕ} (r : R) (w : Prefix n) : ℝ :=
  creationPopulationWeight μ (A.policy r) gapReal q.val w

theorem seedWeight_total {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (n : ℕ) (r : R) :
    (∀ w : Prefix n, 0 ≤ seedWeight μ A q r w) ∧ (∑ w : Prefix n, seedWeight μ A q r w) = 1 :=
  creationPopulationWeight_total μ (A.policy r) gapReal q.val measurable_subtype_coe q.property.1
    (fun d : Gap => ⟨d.property.1.le, d.property.2⟩) q.property.2

theorem measurable_seedWeight {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) {n : ℕ} (w : Prefix n) :
    Measurable (fun r => seedWeight μ A q r w) :=
  measurable_creationPopulationWeight μ A.policy A.policy_measurable _ _ measurable_subtype_coe
    q.property.1 w

private theorem observe_measurable {R : Type} [MeasurableSpace R] (n : ℕ) :
    Measurable (fun z : PopulationSeed R × ProcessTape => (z.1.1, processPrefix n z.2)) :=
  measurable_fst.fst.prodMk
    (measurable_processPrefix Prod.snd ThresholdHC.RareAboveTwo.observable_tape_measurable n)

private theorem kernel_integral {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) (n : ℕ)
    (f : R × Prefix n → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    ∫ z, f (z.1.1, processPrefix n z.2) ∂experimentLaw μ A q =
      ∫ r, ∑ w, seedWeight μ A q r w * f (r, w) ∂A.randomLaw := by
  have hk : Tier5.FiniteKernelRealization A.randomLaw
      ((experimentLaw μ A q).map (fun z => (z.1.1, processPrefix n z.2)))
      (fun r w => creationPopulationWeight μ (A.policy r) gapReal q.val w) :=
    observable_population_prefix_kernel A.randomLaw μ (experimentLaw μ A q) Prod.fst Prod.snd
      A.policy _ q.val measurable_fst ThresholdHC.RareAboveTwo.observable_tape_measurable
      A.policy_measurable measurable_subtype_coe q.property.1
      (fun d : Gap => ⟨d.property.1.le, d.property.2⟩) q.property.2
      (population_realization R μ A q).2 n
  rw [← integral_map (observe_measurable n).aemeasurable hf.aestronglyMeasurable]
  exact hk f hf ⟨C, hC⟩

private theorem bounded_integrable {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) (n : ℕ)
    (f : R × Prefix n → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    Integrable (fun z : PopulationSeed R × ProcessTape => f (z.1.1, processPrefix n z.2))
      (experimentLaw μ A q) :=
  (integrable_const C).mono' (hf.comp (observe_measurable n)).aestronglyMeasurable
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC _)

/-- Exact risk of an estimator whose output reads only the first `n` observations. -/
theorem prefix_output_risk {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (θ : ℝ) (n : ℕ) (g : Prefix n → ℝ)
    (hg : ∀ z, A.output z = g (processPrefix n z.2)) :
    squaredRisk (experimentLaw μ A q) (populationOutput A) θ =
      ENNReal.ofReal (∫ r, ∑ w, seedWeight μ A q r w * (g w - θ)^2 ∂A.randomLaw) := by
  let f : R × Prefix n → ℝ := fun z => (g z.2 - θ)^2
  have hf : Measurable f :=
    (measurable_of_countable (fun w : Prefix n => (g w - θ)^2)).comp measurable_snd
  obtain ⟨C, hC⟩ := (Set.finite_range fun w : Prefix n => |(g w - θ)^2|).bddAbove
  have hb (x : R × Prefix n) : |f x| ≤ C := hC ⟨x.2, rfl⟩
  rw [← kernel_integral μ A q n f hf C hb,
    ofReal_integral_eq_lintegral_ofReal (bounded_integrable μ A q n f hf C hb)
      (ae_of_all _ fun _ => sq_nonneg _)]
  unfold squaredRisk
  apply lintegral_congr
  intro z
  simp only [populationOutput, hg, f]

private theorem clip_sq_le (M θ x : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ M) :
    (clipEstimate M x - θ)^2 ≤ (x - θ)^2 := by
  unfold clipEstimate
  rcases le_total x 0 with h | h
  · rw [min_eq_right (h.trans (hθ.1.trans hθ.2)), max_eq_left h]
    nlinarith
  · rcases le_total x M with h' | h'
    · rw [min_eq_right h', max_eq_right h]
    · rw [min_eq_left h', max_eq_right (hθ.1.trans hθ.2)]
      nlinarith

/-- Under a pathwise cap of `n` flips the policy has stopped after `n`
observations on every valid path. -/
theorem capped_halts {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (n : ℕ)
    (hcap : PathwiseCap A n) (r : R) (x : ProcessTape)
    (hv : ∀ k, (x k).isSome = (A.policy r (processHistory x k)).isSome) :
    A.policy r (processHistory x n) = none := by
  by_contra hne
  have h1 := StoppingProgram.valid_path_continuation_work (A.policy r) x hv n hne
  have h2 := hcap r x hv
  have h3 := h1.trans h2
  rw [show ((n:ℕ):ℝ≥0∞) = ENNReal.ofReal n by simp] at h3
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h3
  linarith

/-- Output clipped to `[0, M]` and read from the padded `n`-prefix. -/
def clippedOutput {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (M : ℝ) {n : ℕ} (r : R)
    (w : Prefix n) : ℝ :=
  clipEstimate M (A.output (r, padPrefix n w))

theorem clippedOutput_mem {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (M : ℝ)
    (hM : 0 ≤ M) {n : ℕ} (r : R) (w : Prefix n) :
    0 ≤ clippedOutput A M r w ∧ clippedOutput A M r w ≤ M :=
  ⟨le_max_left _ _, max_le hM (min_le_left _ _)⟩

theorem measurable_clippedOutput {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (M : ℝ)
    {n : ℕ} (w : Prefix n) : Measurable (fun r => clippedOutput A M r w) :=
  measurable_const.max (measurable_const.min
    (A.output_measurable.comp (measurable_id.prodMk measurable_const)))

/-- Under a pathwise cap of `n` flips, for a target `θ` in `[0, M]`, the risk
is at least that of the clipped prefix estimate. -/
theorem capped_risk_lower {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (n : ℕ) (hcap : PathwiseCap A n) (q : SignLaw) (M θ : ℝ)
    (hθ : 0 ≤ θ ∧ θ ≤ M) :
    ENNReal.ofReal (∫ r, ∑ w : Prefix n, seedWeight μ A q r w * (clippedOutput A M r w - θ)^2
      ∂A.randomLaw) ≤ squaredRisk (experimentLaw μ A q) (populationOutput A) θ := by
  have hM : 0 ≤ M := hθ.1.trans hθ.2
  let f : R × Prefix n → ℝ := fun z => (clippedOutput A M z.1 z.2 - θ)^2
  have hf : Measurable f := by
    have ho : Measurable (fun z : R × Prefix n => A.output (padJoint n z)) :=
      A.output_measurable.comp (measurable_padJoint n)
    exact ((measurable_const.max (measurable_const.min ho)).sub measurable_const).pow_const 2
  have hb (x : R × Prefix n) : |f x| ≤ M^2 := by
    have h := clippedOutput_mem A M hM x.1 x.2
    have e : |f x| = (clippedOutput A M x.1 x.2 - θ)^2 := abs_of_nonneg (sq_nonneg _)
    rw [e]
    nlinarith
  rw [← kernel_integral μ A q n f hf (M^2) hb,
    ofReal_integral_eq_lintegral_ofReal (bounded_integrable μ A q n f hf (M^2) hb)
      (ae_of_all _ fun _ => sq_nonneg _)]
  unfold squaredRisk
  apply lintegral_mono_ae
  filter_upwards [StoppingProgram.original_path_valid μ A q] with z hz
  apply ENNReal.ofReal_le_ofReal
  have hpad := StoppingProgram.valid_path_halt_reconstruction (A.policy z.1.1) z.2 hz n
    (capped_halts A n hcap z.1.1 z.2 hz)
  change (clipEstimate M (A.output (z.1.1, padPrefix n (processPrefix n z.2))) - θ)^2 ≤
    (A.output (z.1.1, z.2) - θ)^2
  rw [hpad]
  exact clip_sq_le _ _ _ hθ

/-- Under `stopAt n p` only full words carry weight, so a sum over the padded
prefixes reduces to a sum over the ordered words. -/
theorem sum_prefix_full (μ : Measure Gap) [IsProbabilityMeasure μ] {n : ℕ} (p : List Bool → ℕ)
    (q : SignLaw) (g : Prefix n → ℝ) :
    ∑ w : Prefix n, creationPopulationWeight μ (stopAt n p) gapReal q.val w * g w =
      ∑ u : Fin n → Bool, creationPopulationWeight μ (stopAt n p) gapReal q.val
        (fun t => some (u t)) * g (fun t => some (u t)) := by
  symm
  apply Fintype.sum_of_injective (fun (u : Fin n → Bool) (t : Fin n) => some (u t))
  · intro u v h
    funext t
    exact Option.some_injective _ (congrFun h t)
  · intro w hw
    have : ∃ t, w t = none := by
      by_contra hc
      push Not at hc
      apply hw
      refine ⟨fun t => (w t).get (Option.isSome_iff_ne_none.mpr (hc t)), ?_⟩
      funext t
      simp
    obtain ⟨t, ht⟩ := this
    rw [stopAt_partial_weight μ p gapReal q.val measurable_subtype_coe q.property.1 w t ht, zero_mul]
  · intro u
    rfl

end ThresholdHC.FiniteBayesAllocation
