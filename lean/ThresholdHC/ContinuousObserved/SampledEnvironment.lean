import ThresholdHC.ContinuousObserved.SampledPolicy
import ThresholdHC.ContinuousObserved.StateParameter

noncomputable section
open MeasureTheory
namespace ThresholdHC.ContinuousObserved
open ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6

def stateSignPrior {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool) (u : unitInterval) : unitInterval :=
  if s (D.cell u) then 1 else 0

theorem stateSignPrior_coe {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool) (u : unitInterval) :
    (stateSignPrior D s u : ℝ) = if s (D.cell u) then 1 else 0 := by
  cases hs : s (D.cell u) <;> simp [stateSignPrior,hs]

theorem measurable_stateSignPrior {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool) :
    Measurable (stateSignPrior D s) :=
  Measurable.ite (positiveState_measurable D s) measurable_const measurable_const

def sampledGap {N : ℕ} {R : Type} (D : QueryDesign N) (z : R × (ℕ → unitInterval)) (i : ℕ) : ℝ :=
  D.gap (z.2 i)

def sampledPrior {N : ℕ} {R : Type} (D : QueryDesign N) (s : Fin N → Bool)
    (z : R × (ℕ → unitInterval)) (i : ℕ) : ℝ := stateSignPrior D s (z.2 i)

def sampledPolicy {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (z : R × (ℕ → unitInterval)) : List Bool → Option ℕ := A.policy z.1

theorem measurable_sampledGap {N : ℕ} {R : Type} [MeasurableSpace R] (D : QueryDesign N) :
    MeasurableEnvironment (sampledGap (R := R) D) := by
  intro i
  exact (measurable_subtype_coe.comp D.gap_measurable).comp
    ((measurable_pi_apply i).comp measurable_snd)

theorem measurable_sampledPrior {N : ℕ} {R : Type} [MeasurableSpace R]
    (D : QueryDesign N) (s : Fin N → Bool) :
    MeasurableEnvironment (sampledPrior (R := R) D s) := by
  intro i
  exact (measurable_subtype_coe.comp (measurable_stateSignPrior D s)).comp
    ((measurable_pi_apply i).comp measurable_snd)

theorem measurable_sampledPolicy {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) :
    MeasurableCreationPolicy (sampledPolicy A) := by
  intro xs i
  exact measurable_fst (A.policy_measurable xs i)

theorem sampledGap_range {N : ℕ} {R : Type} (D : QueryDesign N)
    (z : R × (ℕ → unitInterval)) (i : ℕ) : 0 ≤ sampledGap D z i ∧ sampledGap D z i ≤ 1 / 2 :=
  ⟨(D.gap (z.2 i)).property.1.le,(D.gap (z.2 i)).property.2⟩

theorem sampledPrior_range {N : ℕ} {R : Type} (D : QueryDesign N) (s : Fin N → Bool)
    (z : R × (ℕ → unitInterval)) (i : ℕ) : 0 ≤ sampledPrior D s z i ∧ sampledPrior D s z i ≤ 1 :=
  (stateSignPrior D s (z.2 i)).property

end ThresholdHC.ContinuousObserved
