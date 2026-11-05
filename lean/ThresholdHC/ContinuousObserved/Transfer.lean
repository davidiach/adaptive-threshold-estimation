import ThresholdHC.ContinuousObserved.SampledLaw
import ThresholdHC.Confidence.Model

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservedState

theorem sampled_lintegral {N : ℕ} {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (D : QueryDesign N) (s : Fin N → Bool)
    (hl : volume.map D.gap = μ) (A : AdaptiveEstimator R)
    (P : Measure ((R × (ℕ → unitInterval)) × ProcessTape)) [IsProbabilityMeasure P]
    (hreal : RealizesQueryPrefixes D (sampledStateEstimator A) s P)
    (F : R × ProcessTape → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (z.1.1,z.2) ∂P) =
      ∫⁻ z, F (z.1.1,z.2) ∂experimentLaw μ A (conditionalSign μ D s) := by
  have hs : Measurable (fun z : (R × (ℕ → unitInterval)) × ProcessTape => (z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have ho : Measurable (fun z : PopulationSeed R × ProcessTape => (z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  rw [← lintegral_map hF hs,sampled_observable_law μ D s hl A P hreal,lintegral_map hF ho]

theorem sampled_expectedWork {N : ℕ} {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (D : QueryDesign N) (s : Fin N → Bool)
    (hl : volume.map D.gap = μ) (A : AdaptiveEstimator R)
    (P : Measure ((R × (ℕ → unitInterval)) × ProcessTape)) [IsProbabilityMeasure P]
    (hreal : RealizesQueryPrefixes D (sampledStateEstimator A) s P) :
    (∫⁻ z, totalProcessWork z.2 ∂P) = ThresholdHC.Tier6.expectedWork μ A (conditionalSign μ D s) := by
  apply sampled_lintegral μ D s hl A P hreal (fun z => totalProcessWork z.2)
  exact measurable_totalProcessWork Prod.snd (fun n b =>
    measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd) measurable_const)

theorem sampled_squaredRisk {N : ℕ} {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (D : QueryDesign N) (s : Fin N → Bool)
    (hl : volume.map D.gap = μ) (A : AdaptiveEstimator R)
    (P : Measure ((R × (ℕ → unitInterval)) × ProcessTape)) [IsProbabilityMeasure P]
    (hreal : RealizesQueryPrefixes D (sampledStateEstimator A) s P) :
    squaredRisk P (sampledStateEstimator A).output (stateTarget D.cell s) =
      squaredRisk (experimentLaw μ A (conditionalSign μ D s)) (populationOutput A)
        (signMean μ (conditionalSign μ D s).val) := by
  rw [← conditionalSign_target μ D s hl]
  apply sampled_lintegral μ D s hl A P hreal
    (fun z => ENNReal.ofReal ((A.output z - signMean μ (conditionalSign μ D s).val) ^ 2))
  exact ENNReal.measurable_ofReal.comp ((A.output_measurable.sub_const _).pow_const 2)

theorem sampled_rootMeanRisk {N : ℕ} {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (D : QueryDesign N) (s : Fin N → Bool)
    (hl : volume.map D.gap = μ) (A : AdaptiveEstimator R)
    (P : Measure ((R × (ℕ → unitInterval)) × ProcessTape)) [IsProbabilityMeasure P]
    (hreal : RealizesQueryPrefixes D (sampledStateEstimator A) s P) :
    rootMeanRisk P (sampledStateEstimator A).output (stateTarget D.cell s) =
      rootMeanRisk (experimentLaw μ A (conditionalSign μ D s)) (populationOutput A)
        (signMean μ (conditionalSign μ D s).val) := by
  exact congrArg (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) (sampled_squaredRisk μ D s hl A P hreal)

theorem sampled_failureProbability {N : ℕ} {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (D : QueryDesign N) (s : Fin N → Bool)
    (hl : volume.map D.gap = μ) (A : AdaptiveEstimator R)
    (P : Measure ((R × (ℕ → unitInterval)) × ProcessTape)) [IsProbabilityMeasure P]
    (hreal : RealizesQueryPrefixes D (sampledStateEstimator A) s P) (r : ℝ) :
    P {z | r < |(sampledStateEstimator A).output z - stateTarget D.cell s|} =
      ThresholdHC.Confidence.failureProbability μ A (conditionalSign μ D s) r := by
  rw [← conditionalSign_target μ D s hl]
  let E : Set (R × ProcessTape) :=
    {z | r < |A.output z - signMean μ (conditionalSign μ D s).val|}
  have hE : MeasurableSet E :=
    measurableSet_lt measurable_const ((A.output_measurable.sub_const _).abs)
  have hs : Measurable (fun z : (R × (ℕ → unitInterval)) × ProcessTape => (z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have ho : Measurable (fun z : PopulationSeed R × ProcessTape => (z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have h := congrArg (fun ν : Measure (R × ProcessTape) => ν E) (sampled_observable_law μ D s hl A P hreal)
  rw [Measure.map_apply hs hE,Measure.map_apply ho hE] at h
  exact h

end ThresholdHC.ContinuousObserved
