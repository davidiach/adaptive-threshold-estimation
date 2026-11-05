import ThresholdHC.ContinuousObserved.SampledPrefix
import ThresholdHC.ContinuousObserved.FiniteKernelBridge
import ThresholdHC.Tier5.FiniteCreation

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier5 ThresholdHC.Tier6

/-- Fresh uniform state sampling realizes the original countable-label
population experiment, conditionally on the full sampled outer sequence. -/
theorem sampled_creation_realizes {N : ℕ} {R : Type} [MeasurableSpace R]
    (D : QueryDesign N) (s : Fin N → Bool) (A : AdaptiveEstimator R)
    (P : Measure ((R × (ℕ → unitInterval)) × ProcessTape)) [IsProbabilityMeasure P]
    (hreal : RealizesQueryPrefixes D (sampledStateEstimator A) s P) :
    RealizesCreationPrefixes (A.randomLaw.prod outerSequenceLaw) P Prod.fst Prod.snd
      (sampledPolicy A) (sampledGap D) (sampledPrior D s) := by
  intro n f hf hb
  let p (z : R × (ℕ → unitInterval)) (w : Prefix n) :=
    creationLaw (sampledPolicy A z) (sampledGap D z) (sampledPrior D s z) w
  have hp (w : Prefix n) : Measurable (fun z => p z w) :=
    measurable_creationLaw (sampledPolicy A) (measurable_sampledPolicy A)
      (sampledGap D) (sampledPrior D s) (measurable_sampledGap D) (measurable_sampledPrior D s) w
  have ht (z : R × (ℕ → unitInterval)) : (∀ w, 0 ≤ p z w) ∧ (∑ w, p z w) = 1 :=
    creationLaw_total n (sampledPolicy A z) (sampledGap D z) (sampledPrior D s z)
      (sampledGap_range D z) (sampledPrior_range D s z)
  let Q := P.map (fun z => (z.1,processPrefix n z.2))
  have : IsProbabilityMeasure Q :=
    (Measure.isProbabilityMeasure_map_iff (measurable_jointPrefix n).aemeasurable).mpr inferInstance
  have hk : FiniteKernelRealization (A.randomLaw.prod outerSequenceLaw) Q p := by
    apply finite_kernel_of_lintegral _ _ p hp (fun z w => (ht z).1 w) (fun z => (ht z).2)
    intro F hF
    dsimp only [Q]
    rw [lintegral_map hF (measurable_jointPrefix n),hreal n F hF]
    apply lintegral_congr
    intro z
    exact sampled_prefix_creation_sum D s A z n (fun w => F (z,w))
  have hfm : Measurable (fun z : (R × (ℕ → unitInterval)) × Prefix n => f z.1 z.2) :=
    measurable_from_prod_countable_left hf
  obtain ⟨C,hC⟩ := hb
  have h := hk (fun z => f z.1 z.2) hfm ⟨C,fun z => hC _ _⟩
  dsimp only [Q] at h
  rw [integral_map (measurable_jointPrefix n).aemeasurable hfm.aestronglyMeasurable] at h
  exact h

end ThresholdHC.ContinuousObserved
