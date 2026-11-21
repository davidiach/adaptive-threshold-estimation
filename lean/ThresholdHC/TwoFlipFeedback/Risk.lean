import ThresholdHC.TwoFlipFeedback.TwoGapLaw
import ThresholdHC.CriticalEntropy.ObservablePopulation
import ThresholdHC.Tier6.Full

/-! The mean squared error of the original experiment as a seed average of a
finite sum over the observed words of length two. An estimator whose output is
a function of the first two observations has exactly that risk; for a target
`θ` in `[0, 1/4]`, an estimator under a pathwise cap of two flips has at least
the risk of its clipped output read from the padded two-prefix. -/

noncomputable section
namespace ThresholdHC.TwoFlipFeedback
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open ThresholdHC.HardBudget

/-- Observable horizon-two weight of seed `r` after integrating the hidden
magnitudes and signs. -/
def seedWeight {R : Type} [MeasurableSpace R] (μ : Measure Gap) (A : AdaptiveEstimator R)
    (q : SignLaw) (r : R) (w : Prefix 2) : ℝ :=
  creationPopulationWeight μ (A.policy r) gapValue q.val w

theorem seedWeight_total {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (r : R) :
    (∀ w, 0 ≤ seedWeight μ A q r w) ∧ (∑ w, seedWeight μ A q r w) = 1 :=
  creationPopulationWeight_total μ (A.policy r) gapValue q.val measurable_subtype_coe q.property.1
    (fun d : Gap => ⟨d.property.1.le, d.property.2⟩) q.property.2

theorem measurable_seedWeight {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) (w : Prefix 2) :
    Measurable (fun r => seedWeight μ A q r w) :=
  measurable_creationPopulationWeight μ A.policy A.policy_measurable _ _ measurable_subtype_coe
    q.property.1 w

private theorem observe_measurable {R : Type} [MeasurableSpace R] :
    Measurable (fun z : PopulationSeed R × ProcessTape => (z.1.1, processPrefix 2 z.2)) :=
  measurable_fst.fst.prodMk (measurable_processPrefix Prod.snd ThresholdHC.RareAboveTwo.observable_tape_measurable 2)

private theorem kernel_integral {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    (f : R × Prefix 2 → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    ∫ z, f (z.1.1, processPrefix 2 z.2) ∂experimentLaw μ A q =
      ∫ r, ∑ w, seedWeight μ A q r w * f (r, w) ∂A.randomLaw := by
  have hk : Tier5.FiniteKernelRealization A.randomLaw
      ((experimentLaw μ A q).map (fun z => (z.1.1, processPrefix 2 z.2)))
      (fun r w => creationPopulationWeight μ (A.policy r) gapValue q.val w) :=
    observable_population_prefix_kernel A.randomLaw μ (experimentLaw μ A q) Prod.fst Prod.snd
      A.policy _ q.val measurable_fst ThresholdHC.RareAboveTwo.observable_tape_measurable A.policy_measurable
      measurable_subtype_coe q.property.1 (fun d : Gap => ⟨d.property.1.le, d.property.2⟩)
      q.property.2 (population_realization R μ A q).2 2
  rw [← integral_map observe_measurable.aemeasurable hf.aestronglyMeasurable]
  exact hk f hf ⟨C, hC⟩

private theorem bounded_integrable {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    (f : R × Prefix 2 → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    Integrable (fun z : PopulationSeed R × ProcessTape => f (z.1.1, processPrefix 2 z.2))
      (experimentLaw μ A q) :=
  (integrable_const C).mono' (hf.comp observe_measurable).aestronglyMeasurable
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC _)

/-- Exact risk of an estimator whose output reads only the first two observations. -/
theorem prefix_output_risk {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (θ : ℝ) (g : Prefix 2 → ℝ)
    (hg : ∀ z, A.output z = g (processPrefix 2 z.2)) :
    squaredRisk (experimentLaw μ A q) (populationOutput A) θ =
      ENNReal.ofReal (∫ r, ∑ w, seedWeight μ A q r w * (g w - θ)^2 ∂A.randomLaw) := by
  let f : R × Prefix 2 → ℝ := fun z => (g z.2 - θ)^2
  have hf : Measurable f := (measurable_of_countable (fun w : Prefix 2 => (g w - θ)^2)).comp measurable_snd
  obtain ⟨C, hC⟩ := (Set.finite_range fun w : Prefix 2 => |(g w - θ)^2|).bddAbove
  have hb (x : R × Prefix 2) : |f x| ≤ C := hC ⟨x.2, rfl⟩
  rw [← kernel_integral μ A q f hf C hb,
    ofReal_integral_eq_lintegral_ofReal (bounded_integrable μ A q f hf C hb)
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

/-- Under a pathwise cap of two flips the policy has stopped after two
observations on every valid path. -/
theorem capped_halts {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (hcap : PathwiseCap A 2)
    (r : R) (x : ProcessTape) (hv : ∀ k, (x k).isSome = (A.policy r (processHistory x k)).isSome) :
    A.policy r (processHistory x 2) = none := by
  by_contra hne
  have h1 := StoppingProgram.valid_path_continuation_work (A.policy r) x hv 2 hne
  have h2 := hcap r x hv
  have h3 := h1.trans h2
  rw [show ((2:ℕ):ℝ≥0∞) = ENNReal.ofReal 2 by simp] at h3
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h3
  norm_num at h4

/-- Clipped estimate read from the padded two-prefix. -/
def clippedOutput {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (r : R) (w : Prefix 2) : ℝ :=
  clipEstimate (1/4) (A.output (r, padPrefix 2 w))

theorem clippedOutput_mem {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (r : R)
    (w : Prefix 2) : 0 ≤ clippedOutput A r w ∧ clippedOutput A r w ≤ 1/4 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Under a pathwise cap of two flips, for a target `θ` in `[0, 1/4]`, the risk
is at least that of the clipped prefix estimate. -/
theorem capped_risk_lower {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (hcap : PathwiseCap A 2) (q : SignLaw) (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1/4) :
    ENNReal.ofReal (∫ r, ∑ w, seedWeight μ A q r w * (clippedOutput A r w - θ)^2 ∂A.randomLaw) ≤
      squaredRisk (experimentLaw μ A q) (populationOutput A) θ := by
  let f : R × Prefix 2 → ℝ := fun z => (clippedOutput A z.1 z.2 - θ)^2
  have hf : Measurable f := by
    have ho : Measurable (fun z : R × Prefix 2 => A.output (padJoint 2 z)) :=
      A.output_measurable.comp (measurable_padJoint 2)
    exact ((measurable_const.max (measurable_const.min ho)).sub measurable_const).pow_const 2
  have hb (x : R × Prefix 2) : |f x| ≤ 1/16 := by
    have h := clippedOutput_mem A x.1 x.2
    have e : |f x| = (clippedOutput A x.1 x.2 - θ)^2 := abs_of_nonneg (sq_nonneg _)
    rw [e]
    nlinarith
  rw [← kernel_integral μ A q f hf (1/16) hb,
    ofReal_integral_eq_lintegral_ofReal (bounded_integrable μ A q f hf (1/16) hb)
      (ae_of_all _ fun _ => sq_nonneg _)]
  unfold squaredRisk
  apply lintegral_mono_ae
  filter_upwards [StoppingProgram.original_path_valid μ A q] with z hz
  apply ENNReal.ofReal_le_ofReal
  have hpad := StoppingProgram.valid_path_halt_reconstruction (A.policy z.1.1) z.2 hz 2
    (capped_halts A hcap z.1.1 z.2 hz)
  change (clipEstimate (1/4) (A.output (z.1.1, padPrefix 2 (processPrefix 2 z.2))) - θ)^2 ≤
    (A.output (z.1.1, z.2) - θ)^2
  rw [hpad]
  exact clip_sq_le _ _ _ hθ

/-- The nine words of length two. -/
theorem sum_words (f : Prefix 2 → ℝ) :
    ∑ w, f w = f ![none, none] + f ![none, some false] + f ![none, some true] +
      f ![some false, none] + f ![some false, some false] + f ![some false, some true] +
      f ![some true, none] + f ![some true, some false] + f ![some true, some true] := by
  rw [← (finTwoArrowEquiv (Option Bool)).symm.sum_comp, Fintype.sum_prod_type]
  simp [Fintype.sum_option]
  ring

end ThresholdHC.TwoFlipFeedback
