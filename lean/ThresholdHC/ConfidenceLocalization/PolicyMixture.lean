import ThresholdHC.ConfidenceLocalization.PolicyAuxiliary

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.ConfidenceLocalization
open ThresholdHC.CriticalEntropy

variable {D : Type} [MeasurableSpace D] (μ : Measure D) [IsProbabilityMeasure μ]
  (p₀ p₁ : D → unitInterval)

def localAffinity (B : CappedPolicy) (q r : D → unitInterval) : ℝ :=
  (hellingerAffinity (cappedTranscriptLaw μ B.seedLaw p₀ p₁ q B.procedure B.cap)
    (cappedTranscriptLaw μ B.seedLaw p₀ p₁ r B.procedure B.cap)).toReal

def localNullWork (B : CappedPolicy) : ℝ :=
  (populationExpectedWork μ B.seedLaw p₀ p₁ (fun _ => 0) B.procedure).toReal

omit [IsProbabilityMeasure μ] in
theorem localPolicyOfProcedure_affinity {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) (q r : D → unitInterval) :
    localAffinity μ p₀ p₁ (cappedPolicyOfProcedure ν A m hcap) q r =
      (hellingerAffinity
        (cappedTranscriptLaw μ ν
          p₀ p₁ q A m)
        (cappedTranscriptLaw μ ν
          p₀ p₁ r A m)).toReal := rfl

omit [IsProbabilityMeasure μ] in
theorem localPolicyOfProcedure_nullWork {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) :
    localNullWork μ p₀ p₁ (cappedPolicyOfProcedure ν A m hcap) =
      (populationExpectedWork μ ν
        p₀ p₁ (fun _ => 0) A).toReal := rfl

variable (h₀ : Measurable p₀) (h₁ : Measurable p₁)
include h₀ h₁

/-- Every finite revealed mixture is itself an actual policy. Its components
may have unrelated measurable seed spaces and different deterministic caps. -/
theorem local_policy_mixture {I : Type} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (κ : Measure I) [IsProbabilityMeasure κ] (B : I → CappedPolicy) :
    ∃ M : CappedPolicy,
      localNullWork μ p₀ p₁ M = ∑ i, κ.real {i}*localNullWork μ p₀ p₁ (B i) ∧
      ∀ q r : D → unitInterval, Measurable q → Measurable r →
        localAffinity μ p₀ p₁ M q r = ∑ i, κ.real {i}*localAffinity μ p₀ p₁ (B i) q r := by
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
  · change (populationExpectedWork μ (κ.prod ν) _ _ _ (selectedProcedure A)).toReal = _
    rw [selected_population_work_real μ κ ν _ _ _
      h₀ h₁ measurable_const A m hcap]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    change (populationExpectedWork μ ν _ _ _
      (reseedProcedure (B i).procedure (Function.eval i) (measurable_pi_apply i))).toReal = _
    rw [population_reseed_work μ ν _ _ _
      h₀ h₁ measurable_const,
      (measurePreserving_eval (fun i => (B i).seedLaw) i).map_eq]
    rfl
  · intro q r hq hr
    change (hellingerAffinity (cappedTranscriptLaw μ (κ.prod ν) _ _ q (selectedProcedure A) m)
      (cappedTranscriptLaw μ (κ.prod ν) _ _ r (selectedProcedure A) m)).toReal = _
    rw [selected_affinity μ κ ν _ _ q r
      h₀ h₁ hq hr A m hcap]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    have hBi (z) : (B i).procedure.stop z ≤ m := ((B i).capped z).trans (by exact_mod_cast hm i)
    change (hellingerAffinity (cappedTranscriptLaw μ ν _ _ q
      (reseedProcedure (B i).procedure (Function.eval i) (measurable_pi_apply i)) m)
      (cappedTranscriptLaw μ ν _ _ r
      (reseedProcedure (B i).procedure (Function.eval i) (measurable_pi_apply i)) m)).toReal = _
    rw [reseed_affinity μ ν _ _ q r
      h₀ h₁ hq hr
      (B i).procedure m hBi (Function.eval i) (measurable_pi_apply i),
      (measurePreserving_eval (fun i => (B i).seedLaw) i).map_eq,
      capped_affinity_enlarge μ (B i).seedLaw _ _ q r
        h₀ h₁ hq hr
        (B i).procedure (hm i) (B i).capped]
    rfl


end ThresholdHC.ConfidenceLocalization
