import ThresholdHC.TwoFlipFeedback.Risk

/-! The horizon-two kernel identity of the original experiment: the integral of
a bounded measurable function of the seed and the first two observations is
the seed average of a finite sum over the nine words, weighted by the
observable seed weights. These are copies of private helpers of
`ThresholdHC.TwoFlipFeedback.Risk`, which is not edited. -/

noncomputable section
namespace ThresholdHC.TwoFlipDominance
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open ThresholdHC.TwoFlipFeedback

theorem observe_two_measurable {R : Type} [MeasurableSpace R] :
    Measurable (fun z : PopulationSeed R × ProcessTape => (z.1.1, processPrefix 2 z.2)) :=
  measurable_fst.fst.prodMk
    (measurable_processPrefix Prod.snd ThresholdHC.RareAboveTwo.observable_tape_measurable 2)

theorem prefix_kernel_integral {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    (f : R × Prefix 2 → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    ∫ z, f (z.1.1, processPrefix 2 z.2) ∂experimentLaw μ A q =
      ∫ r, ∑ w, seedWeight μ A q r w * f (r, w) ∂A.randomLaw := by
  have hk : Tier5.FiniteKernelRealization A.randomLaw
      ((experimentLaw μ A q).map (fun z => (z.1.1, processPrefix 2 z.2)))
      (fun r w => creationPopulationWeight μ (A.policy r) gapValue q.val w) :=
    observable_population_prefix_kernel A.randomLaw μ (experimentLaw μ A q) Prod.fst Prod.snd
      A.policy _ q.val measurable_fst ThresholdHC.RareAboveTwo.observable_tape_measurable
      A.policy_measurable measurable_subtype_coe q.property.1
      (fun d : Gap => ⟨d.property.1.le, d.property.2⟩)
      q.property.2 (population_realization R μ A q).2 2
  rw [← integral_map observe_two_measurable.aemeasurable hf.aestronglyMeasurable]
  exact hk f hf ⟨C, hC⟩

theorem prefix_bounded_integrable {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    (f : R × Prefix 2 → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    Integrable (fun z : PopulationSeed R × ProcessTape => f (z.1.1, processPrefix 2 z.2))
      (experimentLaw μ A q) :=
  (integrable_const C).mono' (hf.comp observe_two_measurable).aestronglyMeasurable
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC _)

end ThresholdHC.TwoFlipDominance
