import ThresholdHC.CriticalEntropy.CriticalExperiment
import ThresholdHC.Tier5.StoppingBase

noncomputable section

namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set Filter ThresholdHC.Tier3 ThresholdHC.Tier4
open scoped ENNReal Topology
set_option maxHeartbeats 2000000

theorem critical_tape_measurable {R : Type} [MeasurableSpace R] (k : ℕ) (b : Option Bool) :
    MeasurableSet {z : (R × (ℕ → ℝ)) × ProcessTape | z.2 k = b} :=
  measurableSet_eq_fun ((measurable_pi_apply k).comp measurable_snd) measurable_const

theorem critical_prefix_work_le_total {R : Type} [MeasurableSpace R]
    (A : Tier6.AdaptiveEstimator R) (q : ℝ → unitInterval) (hq : Measurable q)
    (hfin : criticalExpectedWork A q hq < ∞) (n : ℕ) :
    (∫ z, ThresholdHC.workOf (processPrefix n z.2) ∂criticalExperimentLaw A q hq) ≤
      (criticalExpectedWork A q hq).toReal :=
  prefix_work_le_total (criticalExperimentLaw A q hq) Prod.snd critical_tape_measurable hfin n

/-- Finite expected actual work forces termination under this very population.
No termination or absolute continuity from a different population is assumed. -/
theorem critical_experiment_stops {R : Type} [MeasurableSpace R]
    (A : Tier6.AdaptiveEstimator R) (q : ℝ → unitInterval) (hq : Measurable q)
    (hfin : criticalExpectedWork A q hq < ∞) :
    ∀ᵐ z ∂criticalExperimentLaw A q hq, ∃ n, A.policy z.1.1 (processHistory z.2 n) = none := by
  exact Tier5.creation_stops (R × (ℕ → ℝ)) ((R × (ℕ → ℝ)) × ProcessTape)
    (A.randomLaw.prod (Measure.infinitePi (fun _ : ℕ => criticalGapLaw)))
    (criticalExperimentLaw A q hq) Prod.fst Prod.snd
    (fun z : R × (ℕ → ℝ) => A.policy z.1) (fun z i => criticalClippedGap (z.2 i))
    (fun z i => (q (z.2 i) : ℝ)) measurable_fst critical_tape_measurable
    (fun xs a => measurable_fst (A.policy_measurable xs a))
    (criticalExperimentLaw_realizes A q hq) hfin

theorem critical_eventual_tape_reconstruction {R : Type} [MeasurableSpace R]
    (A : Tier6.AdaptiveEstimator R) (q : ℝ → unitInterval) (hq : Measurable q)
    (hfin : criticalExpectedWork A q hq < ∞) :
    ∀ᵐ z ∂criticalExperimentLaw A q hq,
      ∀ᶠ n in atTop, padPrefix n (processPrefix n z.2) = z.2 := by
  have hv : ∀ᵐ z ∂criticalExperimentLaw A q hq, ∀ k,
      (z.2 k).isSome = (A.policy z.1.1 (processHistory z.2 k)).isSome :=
    ae_all_iff.mpr (fun k => Tier5.realized_creation_valid_step
      (A.randomLaw.prod (Measure.infinitePi (fun _ : ℕ => criticalGapLaw)))
      (criticalExperimentLaw A q hq) Prod.fst Prod.snd
      (fun z : R × (ℕ → ℝ) => A.policy z.1) (fun z i => criticalClippedGap (z.2 i))
      (fun z i => (q (z.2 i) : ℝ)) measurable_fst critical_tape_measurable
      (fun xs a => measurable_fst (A.policy_measurable xs a))
      (criticalExperimentLaw_realizes A q hq) k)
  filter_upwards [hv,critical_experiment_stops A q hq hfin] with z hz hstop
  obtain ⟨N,hN⟩ := hstop
  let pol : List Bool → Option (Fin 1) := fun xs => (A.policy z.1.1 xs).map (fun _ => 0)
  have hvflag (k) : (z.2 k).isSome = (pol (processHistory z.2 k)).isSome := by
    simpa only [pol,Option.isSome_map] using hz k
  have hNflag : pol (processHistory z.2 N) = none := by simp [pol,hN]
  have htail := stopped_valid_tail pol z.2 hvflag N hNflag
  exact eventually_atTop.mpr ⟨N,fun n hn => padPrefix_eq_of_tail_none z.2 n
    (fun k hk => htail k (hn.trans hk))⟩

end ThresholdHC.CriticalEntropy
