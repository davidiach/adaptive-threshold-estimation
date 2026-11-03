import ThresholdHC.EntropyTailLower.GatedOutput

/-! Observable early output at the bounded gate time. The early and masked
outputs sum to the original output, with exact mean decomposition under L2.
The signwise early-mean estimate is not asserted here. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

theorem activationGate_rejects_stop {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (M H : ℕ) (z : R × (ℕ → Bool))
    (hz : (activationGate A M H).output z ≠ true) :
    A.stop z = (activationGateCost A M H z:ℕ∞) := by
  have hnot : ¬ (boundaryGateCost M H z.2:ℕ∞) ≤ A.stop z :=
    fun h => hz ((activationGate_accepts_iff A M H z).mpr h)
  exact ((activationGateCost_min A M H z).trans (min_eq_left (le_of_not_ge hnot))).symm

def earlyOutput {R : Type} [MeasurableSpace R] (A : StoppedProcedure R ℝ) (M H : ℕ)
    (z : R × (ℕ → Bool)) : ℝ :=
  if (activationGate A M H).output z = true then 0 else A.output z

theorem measurable_earlyOutput {R : Type} [MeasurableSpace R]
    (A : StoppedProcedure R ℝ) (M H : ℕ) : Measurable (earlyOutput A M H) :=
  measurable_const.ite (measurableSet_eq_fun (activationGate A M H).measurable_output measurable_const)
    A.measurable_output

def earlyProcedure {R : Type} [MeasurableSpace R]
    (A : StoppedProcedure R ℝ) (M H : ℕ) : StoppedProcedure R ℝ :=
  finiteStoppedProcedure (activationGateCost A M H) (earlyOutput A M H)
    (measurable_activationGateCost A M H) (measurable_earlyOutput A M H) (by
      intro r ω ω' he
      have hc := activationGateCost_prefix A M H r ω ω' he
      have hg : (activationGate A M H).output (r,ω) = (activationGate A M H).output (r,ω') :=
        stopped_output_prefix_eq (activationGate A M H) _ r ω ω' le_rfl he
      refine ⟨hc,?_⟩
      unfold earlyOutput
      rw [← hg]
      split_ifs with h
      · rfl
      · exact (stopped_output_prefix_eq A _ r ω ω'
          (activationGate_rejects_stop A M H (r,ω) h).le he).symm)

theorem earlyProcedure_output {R : Type} [MeasurableSpace R]
    (A : StoppedProcedure R ℝ) (M H : ℕ) :
    (earlyProcedure A M H).output = earlyOutput A M H := rfl

theorem earlyProcedure_stop {R : Type} [MeasurableSpace R]
    (A : StoppedProcedure R ℝ) (M H : ℕ) :
    (earlyProcedure A M H).stop = (activationGate A M H).stop := rfl

theorem early_gated_output_sum {R : Type} [MeasurableSpace R]
    (A : StoppedProcedure R ℝ) (M H : ℕ) (z : R × (ℕ → Bool)) :
    (earlyProcedure A M H).output z+(gatedProcedure A M H).output z = A.output z := by
  rw [earlyProcedure_output,gatedProcedure_output]
  simp only [earlyOutput,Set.indicator,Set.mem_ofPred_eq]
  split_ifs <;> simp

theorem earlyProcedure_secondMoment_le {R : Type} [MeasurableSpace R]
    (ν : Measure R) (p : unitInterval) (A : StoppedProcedure R ℝ) (M H : ℕ) :
    conditionalSecondMoment ν p (earlyProcedure A M H) ≤ conditionalSecondMoment ν p A := by
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  change (if (activationGate A M H).output z = true then 0 else A.output z)^2 ≤ (A.output z)^2
  split_ifs <;> nlinarith [sq_nonneg (A.output z)]

theorem early_gated_mean_sum {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R ℝ) (hM : conditionalSecondMoment ν p A ≠ ∞) (M H : ℕ) :
    conditionalMean ν p (earlyProcedure A M H)+conditionalMean ν p (gatedProcedure A M H) =
      conditionalMean ν p A := by
  have he := (conditionalSecondMoment_finite_iff ν p (earlyProcedure A M H)).mp
    (ne_top_of_le_ne_top hM (earlyProcedure_secondMoment_le ν p A M H))
  have hg := (conditionalSecondMoment_finite_iff ν p (gatedProcedure A M H)).mp
    (ne_top_of_le_ne_top hM (gatedProcedure_secondMoment_le ν p A M H))
  have hei : Integrable (earlyProcedure A M H).output (ν.prod (tapeMeasure p)) :=
    ((memLp_map_measure_iff measurable_id.aestronglyMeasurable
      (earlyProcedure A M H).measurable_output.aemeasurable).mp he).integrable (by norm_num)
  have hgi : Integrable (gatedProcedure A M H).output (ν.prod (tapeMeasure p)) :=
    ((memLp_map_measure_iff measurable_id.aestronglyMeasurable
      (gatedProcedure A M H).measurable_output.aemeasurable).mp hg).integrable (by norm_num)
  change (∫ z, (earlyProcedure A M H).output z ∂ν.prod (tapeMeasure p))+
    (∫ z, (gatedProcedure A M H).output z ∂ν.prod (tapeMeasure p)) = _
  rw [← integral_add hei hgi]
  exact integral_congr_ae (ae_of_all _ (early_gated_output_sum A M H))

end ThresholdHC.EntropyTailLower
