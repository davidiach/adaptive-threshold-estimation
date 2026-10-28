import ThresholdHC.CriticalEntropy.CriticalCreation
import ThresholdHC.CriticalEntropy.SeededPopulationTransfer
import ThresholdHC.Tier6.AlgorithmCore
import ThresholdHC.Tier6.Process

noncomputable section

namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set ThresholdHC.Tier3
open scoped ENNReal

/-- The critical population experiment uses the existing Tier 6 canonical
infinite process and the existing observable algorithm type. Clipping merely
defines the gaps off the support of the quadratic law. -/
def criticalExperimentLaw {R : Type} [MeasurableSpace R]
    (A : Tier6.AdaptiveEstimator R) (q : ℝ → unitInterval) (hq : Measurable q) :
    Measure ((R × (ℕ → ℝ)) × ProcessTape) :=
  Tier6.creationProcessLaw (A.randomLaw.prod (Measure.infinitePi (fun _ : ℕ => criticalGapLaw)))
    (fun z => A.policy z.1) (fun z i => criticalClippedGap (z.2 i))
    (fun z i => (q (z.2 i) : ℝ))
    (fun xs a => measurable_fst (A.policy_measurable xs a))
    (fun i => measurable_criticalClippedGap.comp ((measurable_pi_apply i).comp measurable_snd))
    (fun i => measurable_subtype_coe.comp (hq.comp ((measurable_pi_apply i).comp measurable_snd)))
    (fun z i => criticalClippedGap_bounds (z.2 i)) (fun z i => (q (z.2 i)).property)

instance criticalExperimentLaw_probability {R : Type} [MeasurableSpace R]
    (A : Tier6.AdaptiveEstimator R) (q : ℝ → unitInterval) (hq : Measurable q) :
    IsProbabilityMeasure (criticalExperimentLaw A q hq) := by
  unfold criticalExperimentLaw
  exact Tier6.creationProcessLaw_probability _ _ _ _ _ _ _ _ _

def criticalPrefixLaw {R : Type} [MeasurableSpace R]
    (A : Tier6.AdaptiveEstimator R) (q : ℝ → unitInterval) (hq : Measurable q) (n : ℕ) :
    Measure (R × Prefix n) :=
  (criticalExperimentLaw A q hq).map (fun z => (z.1.1,processPrefix n z.2))

def criticalExpectedWork {R : Type} [MeasurableSpace R]
    (A : Tier6.AdaptiveEstimator R) (q : ℝ → unitInterval) (hq : Measurable q) : ℝ≥0∞ :=
  ∫⁻ z, totalProcessWork z.2 ∂criticalExperimentLaw A q hq

theorem criticalExperimentLaw_realizes {R : Type} [MeasurableSpace R]
    (A : Tier6.AdaptiveEstimator R) (q : ℝ → unitInterval) (hq : Measurable q) :
    Tier5.RealizesCreationPrefixes
      (A.randomLaw.prod (Measure.infinitePi (fun _ : ℕ => criticalGapLaw)))
      (criticalExperimentLaw A q hq) Prod.fst Prod.snd
      (fun z => A.policy z.1) (fun z i => criticalClippedGap (z.2 i))
      (fun z i => (q (z.2 i) : ℝ)) :=
  Tier6.creationProcessLaw_realizes _ _ _ _ _ _ _ _ _

/-- One common critical pair controls every finite observable prefix of every
Tier 6 algorithm in the constructed infinite experiment. The pair precedes the
arbitrary seed space and algorithm; all law-realization assumptions are proved. -/
theorem critical_common_experiment_prefix_pair : ∃ C : ℝ, 0 < C ∧
    ∀ (ρ : unitInterval), 0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 →
    ∀ δ : ℝ, 0 ≤ δ → δ ≤ (ρ : ℝ)/96 →
    ∃ (q r : ℝ → unitInterval) (hq : CappedPrior criticalGapLaw (ρ : ℝ) q)
      (hr : CappedPrior criticalGapLaw (ρ : ℝ) r),
      δ ≤ (∫ d, (r d : ℝ) ∂criticalGapLaw)-(∫ d, (q d : ℝ) ∂criticalGapLaw) ∧
      ∀ (R : Type) [MeasurableSpace R] (A : Tier6.AdaptiveEstimator R) (n : ℕ),
        (1-(hellingerAffinity (criticalPrefixLaw A q hq.1 n)
          (criticalPrefixLaw A r hr.1 n)).toReal)*(ρ : ℝ)*criticalLogFactor (ρ : ℝ) ≤
        C*δ^2*∫ z, ThresholdHC.workOf (processPrefix n z.2)
          ∂criticalExperimentLaw A (midpointPrior q r) (measurable_midpointPrior q r hq.1 hr.1) := by
  obtain ⟨C,hC,hcommon⟩ := critical_common_creation_prefix_pair
  refine ⟨C,hC,?_⟩
  intro ρ hρ hρ' δ hδ hδρ
  obtain ⟨q,r,hq,hr,hsep,hpair⟩ := hcommon ρ hρ hρ' δ hδ hδρ
  refine ⟨q,r,hq,hr,hsep,?_⟩
  intro R _ A n
  let s := midpointPrior q r
  have hs : Measurable s := measurable_midpointPrior q r hq.1 hr.1
  have ht (k : ℕ) (b : Option Bool) :
      MeasurableSet {z : (R × (ℕ → ℝ)) × ProcessTape | z.2 k = b} :=
    measurableSet_eq_fun ((measurable_pi_apply k).comp measurable_snd) measurable_const
  have h := observable_population_hellinger_bound A.randomLaw criticalGapLaw
    (criticalExperimentLaw A q hq.1) (criticalExperimentLaw A r hr.1) (criticalExperimentLaw A s hs)
    Prod.fst Prod.snd A.policy criticalClippedGap (fun d => (q d : ℝ))
    (fun d => (r d : ℝ)) (fun d => (s d : ℝ)) measurable_fst ht A.policy_measurable
    measurable_criticalClippedGap (measurable_subtype_coe.comp hq.1)
    (measurable_subtype_coe.comp hr.1) (measurable_subtype_coe.comp hs)
    criticalClippedGap_bounds (fun d => (q d).property) (fun d => (r d).property) (fun d => (s d).property)
    (criticalExperimentLaw_realizes A q hq.1) (criticalExperimentLaw_realizes A r hr.1)
    (criticalExperimentLaw_realizes A s hs) n ((ρ : ℝ)*criticalLogFactor (ρ : ℝ)) (C*δ^2)
    (fun u => by simpa only [mul_assoc] using hpair n (A.policy u))
  simpa only [criticalPrefixLaw,mul_assoc] using h

end ThresholdHC.CriticalEntropy
