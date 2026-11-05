import ThresholdHC.ConfidenceLocalization.StatisticGeometry
import ThresholdHC.CriticalEntropy.SeedAdaptation

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.ConfidenceLocalization
open ThresholdHC.CriticalEntropy

theorem capped_affinity_enlarge {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r)
    (A : StoppedProcedure R E) {m M : ℕ} (h : m ≤ M) (hcap : ∀ z, A.stop z ≤ m) :
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A M)
      (cappedTranscriptLaw μ ν p₀ p₁ r A M)).toReal =
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A m)
      (cappedTranscriptLaw μ ν p₀ p₁ r A m)).toReal := by
  have hcapM (z) : A.stop z ≤ M := (hcap z).trans (by exact_mod_cast h)
  rw [capped_affinity_real μ ν p₀ p₁ q r h₀ h₁ hq hr A M hcapM,
    capped_affinity_real μ ν p₀ p₁ q r h₀ h₁ hq hr A m hcap,
    cappedStatisticLaw_enlarge_cap μ ν p₀ p₁ q h₀ h₁ hq A h hcap,
    cappedStatisticLaw_enlarge_cap μ ν p₀ p₁ r h₀ h₁ hr A h hcap]
  exact realFiniteAffinity_map_injective _ _ _ (statisticCapEmbedding_injective h)

theorem reseed_affinity {D R S E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure S) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (f : S → R) (hf : Measurable f) :
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q (reseedProcedure A f hf) m)
      (cappedTranscriptLaw μ ν p₀ p₁ r (reseedProcedure A f hf) m)).toReal =
    (hellingerAffinity (cappedTranscriptLaw μ (ν.map f) p₀ p₁ q A m)
      (cappedTranscriptLaw μ (ν.map f) p₀ p₁ r A m)).toReal := by
  let : IsProbabilityMeasure (ν.map f) := (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
  rw [capped_affinity_real μ ν p₀ p₁ q r h₀ h₁ hq hr
    (reseedProcedure A f hf) m (fun z => hcap (f z.1,z.2)),
    capped_affinity_real μ (ν.map f) p₀ p₁ q r h₀ h₁ hq hr A m hcap,
    reseed_statistic_law μ ν p₀ p₁ q h₀ h₁ hq A m f hf,
    reseed_statistic_law μ ν p₀ p₁ r h₀ h₁ hr A m f hf]

theorem selected_affinity {D I R E : Type} [Fintype I]
    [MeasurableSpace D] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (κ : Measure I) [IsProbabilityMeasure κ]
    (ν : Measure R) [IsProbabilityMeasure ν] (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r)
    (A : I → StoppedProcedure R E) (m : ℕ) (hcap : ∀ i z, (A i).stop z ≤ m) :
    (hellingerAffinity (cappedTranscriptLaw μ (κ.prod ν) p₀ p₁ q (selectedProcedure A) m)
      (cappedTranscriptLaw μ (κ.prod ν) p₀ p₁ r (selectedProcedure A) m)).toReal =
      ∑ i, κ.real {i}*(hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q (A i) m)
        (cappedTranscriptLaw μ ν p₀ p₁ r (A i) m)).toReal := by
  let ref (i : I) (j : Fin (m+1) × Fin (m+1)) :=
    ((stoppedReference ν (A i) m).map (fun z => stoppedStatistic m z.2)).real {j}
  let lq (j : Fin (m+1) × Fin (m+1)) := (populationWordLikelihood μ p₀ p₁ q j.1.val j.2.val).toReal
  let lr (j : Fin (m+1) × Fin (m+1)) := (populationWordLikelihood μ p₀ p₁ r j.1.val j.2.val).toReal
  have hcellq (i : I) (j : Fin (m+1) × Fin (m+1)) :
      (cappedStatisticLaw μ ν p₀ p₁ q (A i) m).real {j} = lq j*ref i j :=
    cappedStatisticLaw_real_mass μ ν p₀ p₁ q h₀ h₁ hq (A i) m (hcap i) j
  have hcellr (i : I) (j : Fin (m+1) × Fin (m+1)) :
      (cappedStatisticLaw μ ν p₀ p₁ r (A i) m).real {j} = lr j*ref i j :=
    cappedStatisticLaw_real_mass μ ν p₀ p₁ r h₀ h₁ hr (A i) m (hcap i) j
  have hcomponent (i : I) :
      (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q (A i) m)
        (cappedTranscriptLaw μ ν p₀ p₁ r (A i) m)).toReal =
      realFiniteAffinity (fun j => lq j*ref i j) (fun j => lr j*ref i j) := by
    rw [capped_affinity_real μ ν p₀ p₁ q r h₀ h₁ hq hr (A i) m (hcap i)]
    simp_rw [hcellq,hcellr]
  rw [capped_affinity_real μ (κ.prod ν) p₀ p₁ q r h₀ h₁ hq hr
    (selectedProcedure A) m (selectedProcedure_capped A m hcap)]
  simp_rw [selected_statistic_real_mass μ κ ν p₀ p₁ q h₀ h₁ hq A m,
    selected_statistic_real_mass μ κ ν p₀ p₁ r h₀ h₁ hr A m,hcellq,hcellr,hcomponent]
  exact real_affinity_common_density_mixture (fun i => κ.real {i}) (fun i => measureReal_nonneg)
    lq lr ref (fun i j => measureReal_nonneg)

end ThresholdHC.ConfidenceLocalization
