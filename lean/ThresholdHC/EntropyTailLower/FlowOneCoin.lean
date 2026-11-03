import ThresholdHC.CriticalEntropy.SeedAdaptation
import ThresholdHC.StoppingProgram.RealizedOutputs

/-! An actual observable one-coin procedure for a finite flow. The independent
seed chooses a decision table and the output is scaled by root intensity.
Population mean, second moment and work refer to the original tape law. -/

noncomputable section
open MeasureTheory Real
open scoped BigOperators ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper ThresholdHC.ObservableSimulation

def flowCoinSeedLaw {N : ℕ} (f : Flow N) : Measure (CountState N → Bool) :=
  finiteWeightMeasure (decisionWeight (flowDecisionParameters f))

theorem flowCoinSeedLaw_probability {N : ℕ} (f : Flow N) (hf : FlowCone f) :
    IsProbabilityMeasure (flowCoinSeedLaw f) :=
  finiteWeightMeasure_probability _ (flow_mixture_probability f hf).1 (flow_mixture_probability f hf).2

def flowCoinProcedure {N : ℕ} (hN : 0 < N) (f : Flow N) :
    StoppedProcedure (CountState N → Bool) ℝ :=
  finiteStoppedProcedure (fun z => tableCost z.1 z.2)
    (fun z => intensity f*tableValue z.1 (flowTableOutput f) z.2)
    (measurable_from_prod_countable_right (fun b => (tableCall hN b (flowTableOutput f)).measurable_cost))
    (measurable_const.mul (measurable_from_prod_countable_right
      (fun b => (tableCall hN b (flowTableOutput f)).measurable_value)))
    (fun b ω ω' he => by
      have h := (tableCall hN b (flowTableOutput f)).prefix_ext ω ω' he
      exact ⟨h.1,congrArg (fun x => intensity f*x) h.2⟩)

theorem flowCoinProcedure_capped {N : ℕ} (hN : 0 < N) (f : Flow N)
    (z : (CountState N → Bool) × (ℕ → Bool)) : (flowCoinProcedure hN f).stop z ≤ N := by
  change (tableCost z.1 z.2 : ℕ∞) ≤ N
  exact_mod_cast tableCall_cost_le hN z.1 (flowTableOutput f) z.2

theorem flowCoinProcedure_output_bound {N : ℕ} (hN : 0 < N) (f : Flow N)
    (z : (CountState N → Bool) × (ℕ → Bool)) :
    ‖(flowCoinProcedure hN f).output z‖ ≤ ‖intensity f‖*(∑ s, ‖flowTableOutput f s‖) := by
  change ‖intensity f*tableValue z.1 (flowTableOutput f) z.2‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (tableValue_bounded _ _ _) (norm_nonneg _)

theorem finite_seed_integral {I Ω : Type} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace Ω]
    (κ : Measure I) [IsProbabilityMeasure κ] (τ : Measure Ω) [IsProbabilityMeasure τ]
    (F : I × Ω → ℝ) (hF : Measurable F) (M : ℝ) (hbound : ∀ z, ‖F z‖ ≤ M) :
    (∫ z, F z ∂κ.prod τ) = ∑ i, κ.real {i}*(∫ ω, F (i,ω) ∂τ) := by
  have hi : Integrable F (κ.prod τ) := Integrable.of_bound hF.aestronglyMeasurable M (ae_of_all _ hbound)
  rw [integral_prod F hi,integral_fintype hi.integral_prod_left]
  simp only [smul_eq_mul,measureReal_def]

theorem flowCoinProcedure_mean {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (hN : 0 < N) (f : Flow N) (hf : FlowCone f) :
    (∫ z, (flowCoinProcedure hN f).output z ∂(flowCoinSeedLaw f).prod (originalPopulationTapeLaw μ q)) =
      countMean μ q f.outputWeight := by
  let := flowCoinSeedLaw_probability f hf
  have hb (z : (CountState N → Bool) × (ℕ → Bool)) :
      ‖(flowCoinProcedure hN f).output z‖ ≤ ‖intensity f‖*(∑ s, ‖flowTableOutput f s‖) := by
    change ‖intensity f*tableValue z.1 (flowTableOutput f) z.2‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (tableValue_bounded _ _ _) (norm_nonneg _)
  rw [finite_seed_integral _ _ _ (flowCoinProcedure hN f).measurable_output _ hb]
  have hw := (flow_mixture_probability f hf).1
  simp only [flowCoinSeedLaw,finiteWeightMeasure_real_singleton _ hw]
  change (∑ b, decisionWeight (flowDecisionParameters f) b*
    (∫ ω, intensity f*tableValue b (flowTableOutput f) ω ∂originalPopulationTapeLaw μ q)) = _
  simp_rw [integral_const_mul]
  have he : (∑ b, decisionWeight (flowDecisionParameters f) b*
      (intensity f*(∫ ω, tableValue b (flowTableOutput f) ω ∂originalPopulationTapeLaw μ q))) =
      ∑ b, flowTableRate f b*(∫ ω, tableValue b (flowTableOutput f) ω ∂originalPopulationTapeLaw μ q) :=
    Finset.sum_congr rfl (fun _ _ => by unfold flowTableRate; ring)
  rw [he,flow_output_mean μ q f hf hN]

theorem flowCoinProcedure_moment {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (hN : 0 < N) (f : Flow N) (hf : FlowCone f) :
    (∫ z, ((flowCoinProcedure hN f).output z)^2 ∂(flowCoinSeedLaw f).prod (originalPopulationTapeLaw μ q)) ≤
      intensity f*countMean μ q f.momentWeight := by
  let := flowCoinSeedLaw_probability f hf
  let M := ‖intensity f‖*(∑ s, ‖flowTableOutput f s‖)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hb (z) : ‖((flowCoinProcedure hN f).output z)^2‖ ≤ M^2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (flowCoinProcedure_output_bound hN f z) 2
  rw [finite_seed_integral _ _ _ ((flowCoinProcedure hN f).measurable_output.pow_const 2) _ hb]
  have hw := (flow_mixture_probability f hf).1
  simp only [flowCoinSeedLaw,finiteWeightMeasure_real_singleton _ hw]
  change (∑ b, decisionWeight (flowDecisionParameters f) b*
    (∫ ω, (intensity f*tableValue b (flowTableOutput f) ω)^2 ∂originalPopulationTapeLaw μ q)) ≤ _
  simp_rw [mul_pow,integral_const_mul]
  have he : (∑ b, decisionWeight (flowDecisionParameters f) b*
      ((intensity f)^2*(∫ ω, (tableValue b (flowTableOutput f) ω)^2 ∂originalPopulationTapeLaw μ q))) =
      intensity f*(∑ b, flowTableRate f b*(∫ ω, (tableValue b (flowTableOutput f) ω)^2 ∂originalPopulationTapeLaw μ q)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by unfold flowTableRate; ring)
  rw [he]
  exact mul_le_mul_of_nonneg_left (flow_output_second_moment μ q f hf hN) (hf.continue_nonneg _)

theorem flowCoinProcedure_work_integral {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (hN : 0 < N) (f : Flow N) (hf : FlowCone f) (hi : 0 < intensity f) :
    (∫ z, (tableCost z.1 z.2:ℝ) ∂(flowCoinSeedLaw f).prod (originalPopulationTapeLaw μ q)) =
      countMean μ q f.continueWeight/intensity f := by
  let := flowCoinSeedLaw_probability f hf
  have hm : Measurable (fun z : (CountState N → Bool) × (ℕ → Bool) => (tableCost z.1 z.2:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
      (measurable_from_prod_countable_right (fun b => (tableCall hN b (flowTableOutput f)).measurable_cost))
  have hb (z : (CountState N → Bool) × (ℕ → Bool)) : ‖(tableCost z.1 z.2:ℝ)‖ ≤ (N:ℝ) := by
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast tableCall_cost_le hN z.1 (flowTableOutput f) z.2
  rw [finite_seed_integral _ _ _ hm _ hb]
  have hw := (flow_mixture_probability f hf).1
  simp only [flowCoinSeedLaw,finiteWeightMeasure_real_singleton _ hw]
  apply (eq_div_iff hi.ne').mpr
  rw [Finset.sum_mul]
  have he : (∑ b, decisionWeight (flowDecisionParameters f) b*
      (∫ ω, (tableCost b ω:ℝ) ∂originalPopulationTapeLaw μ q)*intensity f) =
      ∑ b, flowTableRate f b*(∫ ω, (tableCost b ω:ℝ) ∂originalPopulationTapeLaw μ q) :=
    Finset.sum_congr rfl (fun _ _ => by unfold flowTableRate; ring)
  rw [he,flow_mixture_work μ q f hf hN]

theorem flowCoinProcedure_population_mean {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (hN : 0 < N) (f : Flow N) (hf : FlowCone f) :
    populationMean μ (flowCoinSeedLaw f) (gapParameter false) (gapParameter true) (signUnit q)
      (flowCoinProcedure hN f) = countMean μ q f.outputWeight := by
  let := flowCoinSeedLaw_probability f hf
  have hp := populationInput_preserving μ (flowCoinSeedLaw f) _ _ (signUnit q)
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)
  change (∫ z, (flowCoinProcedure hN f).output (populationInput _ _ _ z) ∂populationMeasure μ _) = _
  have he := integral_map (μ := populationMeasure μ (flowCoinSeedLaw f))
    hp.measurable.aemeasurable (flowCoinProcedure hN f).measurable_output.aestronglyMeasurable
  rw [hp.map_eq] at he
  rw [← he]
  exact flowCoinProcedure_mean μ q hN f hf

theorem flowCoinProcedure_population_moment {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (hN : 0 < N) (f : Flow N) (hf : FlowCone f) :
    populationSecondMoment μ (flowCoinSeedLaw f) (gapParameter false) (gapParameter true) (signUnit q)
      (flowCoinProcedure hN f) ≤ ENNReal.ofReal (intensity f*countMean μ q f.momentWeight) := by
  let := flowCoinSeedLaw_probability f hf
  have hp := populationInput_preserving μ (flowCoinSeedLaw f) _ _ (signUnit q)
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)
  let M := ‖intensity f‖*(∑ s, ‖flowTableOutput f s‖)
  have hi : Integrable (fun z => ((flowCoinProcedure hN f).output z)^2)
      ((flowCoinSeedLaw f).prod (originalPopulationTapeLaw μ q)) := by
    apply Integrable.of_bound ((flowCoinProcedure hN f).measurable_output.pow_const 2).aestronglyMeasurable (M^2)
    apply ae_of_all
    intro z
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (flowCoinProcedure_output_bound hN f z) 2
  change (∫⁻ z, ENNReal.ofReal (((flowCoinProcedure hN f).output (populationInput _ _ _ z))^2) ∂populationMeasure μ _) ≤ _
  have hF : Measurable (fun z => ENNReal.ofReal (((flowCoinProcedure hN f).output z)^2)) :=
    ENNReal.measurable_ofReal.comp ((flowCoinProcedure hN f).measurable_output.pow_const 2)
  rw [hp.lintegral_comp hF]
  change (∫⁻ z, ENNReal.ofReal (((flowCoinProcedure hN f).output z)^2) ∂(flowCoinSeedLaw f).prod (originalPopulationTapeLaw μ q)) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (flowCoinProcedure_moment μ q hN f hf)

theorem flowCoinProcedure_population_work {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (hN : 0 < N) (f : Flow N) (hf : FlowCone f) (hi : 0 < intensity f) :
    populationExpectedWork μ (flowCoinSeedLaw f) (gapParameter false) (gapParameter true) (signUnit q)
      (flowCoinProcedure hN f) = ENNReal.ofReal (countMean μ q f.continueWeight/intensity f) := by
  let := flowCoinSeedLaw_probability f hf
  rw [populationInput_work μ _ _ _ _ (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)]
  have he (z : (CountState N → Bool) × (ℕ → Bool)) :
      stoppedProcedureWork (flowCoinProcedure hN f) z = ENNReal.ofReal (tableCost z.1 z.2:ℝ) := by
    simp [flowCoinProcedure,finiteStoppedProcedure,stoppedProcedureWork]
  simp_rw [he]
  have hm : Measurable (fun z : (CountState N → Bool) × (ℕ → Bool) => (tableCost z.1 z.2:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
      (measurable_from_prod_countable_right (fun b => (tableCall hN b (flowTableOutput f)).measurable_cost))
  have hi' : Integrable (fun z : (CountState N → Bool) × (ℕ → Bool) => (tableCost z.1 z.2:ℝ))
      ((flowCoinSeedLaw f).prod (originalPopulationTapeLaw μ q)) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (N:ℝ)
    apply ae_of_all
    intro z
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast tableCall_cost_le hN z.1 (flowTableOutput f) z.2
  change (∫⁻ z, ENNReal.ofReal (tableCost z.1 z.2:ℝ) ∂(flowCoinSeedLaw f).prod (originalPopulationTapeLaw μ q)) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hi' (ae_of_all _ (fun _ => Nat.cast_nonneg _)),
    flowCoinProcedure_work_integral μ q hN f hf hi]

end ThresholdHC.EntropyTailLower
