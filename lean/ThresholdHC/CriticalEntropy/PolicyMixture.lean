import ThresholdHC.CriticalEntropy.SeedAdaptation

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

/-- A capped observable acquisition policy, including its independent seed law.
Outputs can be forgotten because the full seed/transcript remains observed. -/
structure CappedPolicy where
  Seed : Type
  [measurableSeed : MeasurableSpace Seed]
  seedLaw : Measure Seed
  [probability : IsProbabilityMeasure seedLaw]
  procedure : StoppedProcedure Seed Unit
  cap : ℕ
  capped : ∀ z, procedure.stop z ≤ cap

attribute [instance] CappedPolicy.measurableSeed CappedPolicy.probability

def cappedPolicyOfProcedure {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) : CappedPolicy where
  Seed := R
  seedLaw := ν
  procedure := postprocessProcedure A (fun _ => ()) measurable_const
  cap := m
  capped := hcap

def policyAffinity (B : CappedPolicy) (q r : ℝ → unitInterval) : ℝ :=
  (hellingerAffinity
    (cappedTranscriptLaw criticalGapLaw B.seedLaw
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q B.procedure B.cap)
    (cappedTranscriptLaw criticalGapLaw B.seedLaw
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) r B.procedure B.cap)).toReal

def policyNullWork (B : CappedPolicy) : ℝ :=
  (populationExpectedWork criticalGapLaw B.seedLaw
    (fun d => criticalParameter d false) (fun d => criticalParameter d true)
    (fun _ => 0) B.procedure).toReal

theorem cappedPolicyOfProcedure_affinity {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) (q r : ℝ → unitInterval) :
    policyAffinity (cappedPolicyOfProcedure ν A m hcap) q r =
      (hellingerAffinity
        (cappedTranscriptLaw criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m)
        (cappedTranscriptLaw criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) r A m)).toReal := rfl

theorem cappedPolicyOfProcedure_nullWork {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) :
    policyNullWork (cappedPolicyOfProcedure ν A m hcap) =
      (populationExpectedWork criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) (fun _ => 0) A).toReal := rfl

/-- Every finite revealed mixture is itself an actual policy. Its components
may have unrelated measurable seed spaces and different deterministic caps. -/
theorem capped_policy_mixture {I : Type} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (κ : Measure I) [IsProbabilityMeasure κ] (B : I → CappedPolicy) :
    ∃ M : CappedPolicy,
      policyNullWork M = ∑ i, κ.real {i}*policyNullWork (B i) ∧
      ∀ q r : ℝ → unitInterval, Measurable q → Measurable r →
        policyAffinity M q r = ∑ i, κ.real {i}*policyAffinity (B i) q r := by
  classical
  let R := (i : I) → (B i).Seed
  let ν : Measure R := Measure.pi (fun i => (B i).seedLaw)
  let A (i : I) : StoppedProcedure R Unit :=
    reseedProcedure (B i).procedure (Function.eval i) (measurable_pi_apply i)
  let m := ∑ i, (B i).cap
  have hm (i : I) : (B i).cap ≤ m :=
    Finset.single_le_sum (f := fun j => (B j).cap) (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
  have hcap (i : I) (z) : (A i).stop z ≤ m :=
    ((B i).capped (z.1 i,z.2)).trans (by exact_mod_cast hm i)
  let M : CappedPolicy := {
    Seed := I × R
    seedLaw := κ.prod ν
    procedure := selectedProcedure A
    cap := m
    capped := selectedProcedure_capped A m hcap }
  refine ⟨M,?_,?_⟩
  · change (populationExpectedWork criticalGapLaw (κ.prod ν) _ _ _ (selectedProcedure A)).toReal = _
    rw [selected_population_work_real criticalGapLaw κ ν _ _ _
      (measurable_criticalParameter false) (measurable_criticalParameter true) measurable_const A m hcap]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    change (populationExpectedWork criticalGapLaw ν _ _ _
      (reseedProcedure (B i).procedure (Function.eval i) (measurable_pi_apply i))).toReal = _
    rw [population_reseed_work criticalGapLaw ν _ _ _
      (measurable_criticalParameter false) (measurable_criticalParameter true) measurable_const,
      (measurePreserving_eval (fun i => (B i).seedLaw) i).map_eq]
    rfl
  · intro q r hq hr
    change (hellingerAffinity (cappedTranscriptLaw criticalGapLaw (κ.prod ν) _ _ q (selectedProcedure A) m)
      (cappedTranscriptLaw criticalGapLaw (κ.prod ν) _ _ r (selectedProcedure A) m)).toReal = _
    rw [selected_affinity_real criticalGapLaw κ ν _ _ q r
      (measurable_criticalParameter false) (measurable_criticalParameter true) hq hr A m hcap
      critical_parameters_interior]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    have hBi (z) : (B i).procedure.stop z ≤ m := ((B i).capped z).trans (by exact_mod_cast hm i)
    change (hellingerAffinity (cappedTranscriptLaw criticalGapLaw ν _ _ q
      (reseedProcedure (B i).procedure (Function.eval i) (measurable_pi_apply i)) m)
      (cappedTranscriptLaw criticalGapLaw ν _ _ r
      (reseedProcedure (B i).procedure (Function.eval i) (measurable_pi_apply i)) m)).toReal = _
    rw [reseed_affinity_real criticalGapLaw ν _ _ q r
      (measurable_criticalParameter false) (measurable_criticalParameter true) hq hr
      (B i).procedure m hBi (Function.eval i) (measurable_pi_apply i) critical_parameters_interior,
      (measurePreserving_eval (fun i => (B i).seedLaw) i).map_eq,
      capped_affinity_enlarge_cap criticalGapLaw (B i).seedLaw _ _ q r
        (measurable_criticalParameter false) (measurable_criticalParameter true) hq hr
        (B i).procedure (hm i) (B i).capped critical_parameters_interior]
    rfl

end ThresholdHC.CriticalEntropy
