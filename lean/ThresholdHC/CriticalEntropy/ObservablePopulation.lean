import ThresholdHC.CriticalEntropy.SeedAffinity
import ThresholdHC.CriticalEntropy.CreationPopulation

noncomputable section

namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set ThresholdHC.Tier3 ThresholdHC.Tier4
open scoped ENNReal

/-- Marginalize the iid hidden environment from an actual realization of the
existing unrestricted-creation experiment. Only the original seed and observed
prefix remain in the law. -/
theorem observable_population_prefix_kernel {R D Ω : Type}
    [MeasurableSpace R] [MeasurableSpace D] [MeasurableSpace Ω]
    (ν : Measure R) [IsProbabilityMeasure ν] (μ : Measure D) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (seed : Ω → R × (ℕ → D)) (tape : Ω → ProcessTape)
    (pol : R → List Bool → Option ℕ) (d q : D → ℝ)
    (hs : Measurable seed) (ht : ∀ n b, MeasurableSet {ω | tape ω n = b})
    (hp : Tier5.MeasurableCreationPolicy pol) (hdm : Measurable d) (hqm : Measurable q)
    (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2) (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1)
    (hreal : Tier5.RealizesCreationPrefixes (ν.prod (Measure.infinitePi (fun _ : ℕ => μ)))
      P seed tape (fun z => pol z.1) (fun z i => d (z.2 i)) (fun z i => q (z.2 i))) (n : ℕ) :
    Tier5.FiniteKernelRealization ν
      (P.map (fun ω => ((seed ω).1,processPrefix n (tape ω))))
      (fun r w => creationPopulationWeight μ (pol r) d q w) := by
  let κ := Measure.infinitePi (fun _ : ℕ => μ)
  let p (z : R × (ℕ → D)) (w : Prefix n) :=
    Tier5.creationLaw (pol z.1) (fun i => d (z.2 i)) (fun i => q (z.2 i)) w
  have hpm (w : Prefix n) : Measurable (fun z => p z w) :=
    Tier5.measurable_creationLaw (fun z : R × (ℕ → D) => pol z.1)
      (fun xs a => measurable_fst (hp xs a))
      (fun z i => d (z.2 i)) (fun z i => q (z.2 i))
      (fun i => hdm.comp ((measurable_pi_apply i).comp measurable_snd))
      (fun i => hqm.comp ((measurable_pi_apply i).comp measurable_snd)) w
  have htotal (z : R × (ℕ → D)) := Tier5.creationLaw_total n (pol z.1)
    (fun i => d (z.2 i)) (fun i => q (z.2 i)) (fun i => hd _) (fun i => hq _)
  have hp0 (z : R × (ℕ → D)) (w : Prefix n) : 0 ≤ p z w := (htotal z).1 w
  have hp1 (z : R × (ℕ → D)) (w : Prefix n) : p z w ≤ 1 := by
    rw [← (htotal z).2]
    exact Finset.single_le_sum (fun v hv => hp0 z v) (Finset.mem_univ w)
  have hk := Tier5.realized_creation_prefix_kernel (ν.prod κ) P seed tape
    (fun z => pol z.1) (fun z i => d (z.2 i)) (fun z i => q (z.2 i)) hs ht hreal n
  have h := finite_kernel_marginal ν κ (prefixTranscriptLaw P seed tape n) p hpm hp0 hp1 hk
  have hproj : Measurable (fun z : (R × (ℕ → D)) × Prefix n => (z.1.1,z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  rw [prefixTranscriptLaw,Measure.map_map hproj (hs.prodMk (measurable_processPrefix tape ht n))] at h
  exact h

end ThresholdHC.CriticalEntropy
