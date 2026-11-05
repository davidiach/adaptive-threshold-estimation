import ThresholdHC.ContinuousObserved.ConditionalSign

noncomputable section
open MeasureTheory Set
namespace ThresholdHC.ContinuousObserved
open ThresholdHC.Tier6 ThresholdHC.ObservedState ThresholdHC.ObservableSimulation
open ThresholdHC.CriticalEntropy

def stateParameter {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool) (u : unitInterval) : unitInterval :=
  gapParameter (s (D.cell u)) (D.gap u)

theorem positiveState_measurable {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool) :
    MeasurableSet {u : unitInterval | s (D.cell u) = true} :=
  measurableSet_eq_fun ((measurable_of_countable s).comp D.cell_measurable) measurable_const

theorem measurable_stateParameter {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool) :
    Measurable (stateParameter D s) := by
  have he : stateParameter D s = (fun u =>
      if s (D.cell u) = true then gapParameter true (D.gap u) else gapParameter false (D.gap u)) := by
    funext u
    cases hs : s (D.cell u) <;> simp [stateParameter,hs]
  rw [he]
  exact Measurable.ite (positiveState_measurable D s)
    ((measurable_gapParameter true).comp D.gap_measurable)
    ((measurable_gapParameter false).comp D.gap_measurable)

theorem conditionalSign_target {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (D : QueryDesign N) (s : Fin N → Bool) (hl : volume.map D.gap = μ) :
    signMean μ (conditionalSign μ D s).val = stateTarget D.cell s := by
  have he := conditionalSign_positive_integral μ D s hl (fun _ => 1) measurable_const
  simpa [signMean,stateTarget] using he

/-- The original population model represents every deterministic observed-state
model after integrating its conditional sign probability at each gap. -/
theorem state_parameter_law {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (D : QueryDesign N) (s : Fin N → Bool) (hl : volume.map D.gap = μ) :
    volume.map (stateParameter D s) =
      populationParameterLaw μ (gapParameter false) (gapParameter true) (signUnit (conditionalSign μ D s)) := by
  let q := conditionalSign μ D s
  have : IsProbabilityMeasure
      (populationParameterLaw μ (gapParameter false) (gapParameter true) (signUnit q)) :=
    populationParameterLaw_probability μ _ _ _ (measurable_gapParameter false)
      (measurable_gapParameter true) (measurable_signUnit q)
  apply measure_eq_of_bounded_real_tests
  intro F hF hbound
  obtain ⟨C,hC⟩ := hbound
  rw [integral_map (measurable_stateParameter D s).aemeasurable hF.aestronglyMeasurable,
    populationParameterLaw_integral μ _ _ _ (measurable_gapParameter false)
      (measurable_gapParameter true) (measurable_signUnit q) F hF C hC]
  let Fm (d : Gap) := F (gapParameter false d)
  let H (d : Gap) := F (gapParameter true d) - Fm d
  have hm : Measurable Fm := hF.comp (measurable_gapParameter false)
  have hH : Measurable H := (hF.comp (measurable_gapParameter true)).sub hm
  have hHb (d : Gap) : |H d| ≤ 2 * C :=
    (abs_sub _ _).trans (by dsimp [Fm]; linarith [hC (gapParameter true d),hC (gapParameter false d)])
  have hiM : Integrable Fm μ := ThresholdHC.Tier5.integrable_of_abs_bound _ _ hm C (fun d => hC _)
  have hiQ : Integrable (fun d => q.val d * H d) μ := by
    apply ThresholdHC.Tier5.integrable_of_abs_bound _ _ (q.property.1.mul hH) (2 * C)
    intro d
    change |q.val d * H d| ≤ 2 * C
    rw [abs_mul,abs_of_nonneg (q.property.2 d).1]
    exact (mul_le_of_le_one_left (abs_nonneg _) (q.property.2 d).2).trans (hHb d)
  have hiMU : Integrable (fun u => Fm (D.gap u)) (volume : Measure unitInterval) :=
    ThresholdHC.Tier5.integrable_of_abs_bound _ _ (hm.comp D.gap_measurable) C (fun u => hC _)
  have hiHU : Integrable (fun u => H (D.gap u)) (volume : Measure unitInterval) :=
    ThresholdHC.Tier5.integrable_of_abs_bound _ _ (hH.comp D.gap_measurable) (2 * C) (fun u => hHb _)
  have he : (fun u => F (stateParameter D s u)) =
      (fun u => Fm (D.gap u) + {u | s (D.cell u) = true}.indicator (fun u => H (D.gap u)) u) := by
    funext u
    cases hs : s (D.cell u) <;> simp [stateParameter,hs,Fm,H]
  rw [he,integral_add hiMU (hiHU.indicator (positiveState_measurable D s)),
    integral_indicator (positiveState_measurable D s),
    ← conditionalSign_positive_integral μ D s hl H hH]
  have hmap : (∫ u : unitInterval, Fm (D.gap u)) = ∫ d, Fm d ∂μ := by
    rw [← integral_map D.gap_measurable.aemeasurable hm.aestronglyMeasurable,hl]
  rw [hmap,← integral_add hiM hiQ]
  apply integral_congr_ae
  apply ae_of_all
  intro d
  dsimp [Fm,H,signUnit]
  ring

end ThresholdHC.ContinuousObserved
