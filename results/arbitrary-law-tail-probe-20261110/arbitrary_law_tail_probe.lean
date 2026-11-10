
import ThresholdHC.ArbitraryLawAdaptation.TailProbeLaw
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Real ProbabilityTheory
open scoped ENNReal
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.Tier2 ThresholdHC.Tier6
open ThresholdHC.Uniform713 ThresholdHC.EntropyTailUpper ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation

example : ∀ (J : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ),
    probeWork J ω n = ∑ i ∈ Finset.range n, tailWork J (ω i) := fun _ _ _ => rfl
example : ∀ (J M : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ), probeAdmits J M ω n ↔
    n ≤ M ∧ ∀ i, i + 1 < n → ¬ tailUnresolved J (ω i) := fun _ _ _ _ => Iff.rfl
example : ∀ (J M : ℕ) (ω : ℕ → ℕ → Bool),
    probeHorizon J M ω = sSup {n | probeAdmits J M ω n} := fun _ _ _ => rfl
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ), probeReaches J b M ω n ↔
    probeAdmits J M ω n ∧ probeWork J ω n ≤ b := fun _ _ _ _ _ => Iff.rfl
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeCompleted J b M ω = sSup {n | probeReaches J b M ω n} := fun _ _ _ _ => rfl
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeFlips J b M ω = min b (probeWork J ω (probeHorizon J M ω)) := fun _ _ _ _ => rfl
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool), probeUnresolved J b M ω ↔
    0 < probeCompleted J b M ω ∧ tailUnresolved J (ω (probeCompleted J b M ω - 1)) :=
  fun _ _ _ _ => Iff.rfl
example : ∀ n : ℕ, probeUpper n = if n = 0 then (1 : ℝ) else min 1 (8 / (n : ℝ)) :=
  fun _ => rfl

example : ∀ (J : ℕ) (ω : ℕ → ℕ → Bool),
    probeWork J ω 0 = 0 := @probeWork_zero
example : ∀ (J : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ),
    probeWork J ω (n + 1) = probeWork J ω n + tailWork J (ω n) := @probeWork_succ
example : ∀ (J : ℕ) (ω : ℕ → ℕ → Bool) {n n' : ℕ} (h : n ≤ n'),
    probeWork J ω n ≤ probeWork J ω n' := @probeWork_mono
example : ∀ (J : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ),
    n ≤ probeWork J ω n := @le_probeWork
example : ∀ (J : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ),
    probeWork J ω n ≤ n * 4 ^ J := @probeWork_le
example : ∀ (J : ℕ) (ω : ℕ → ℕ → Bool) {n n' : ℕ} (h : n < n'),
    probeWork J ω n < probeWork J ω n' := @probeWork_strictMono
example : ∀ {J n : ℕ} {ω ω' : ℕ → ℕ → Bool} (h : ∀ i < n, ∀ k < tailWork J (ω i), ω i k = ω' i k),
    probeWork J ω' n = probeWork J ω n := @probeWork_congr
example : ∀ (J M : ℕ) (ω : ℕ → ℕ → Bool),
    probeAdmits J M ω 0 := @probeAdmits_zero
example : ∀ {J M : ℕ} {ω : ℕ → ℕ → Bool} {n n' : ℕ} (h : probeAdmits J M ω n) (hn : n' ≤ n),
    probeAdmits J M ω n' := @probeAdmits_of_le
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeReaches J b M ω 0 := @probeReaches_zero
example : ∀ {J b M : ℕ} {ω : ℕ → ℕ → Bool} {n n' : ℕ} (h : probeReaches J b M ω n) (hn : n' ≤ n),
    probeReaches J b M ω n' := @probeReaches_of_le
example : ∀ (J M : ℕ) (ω : ℕ → ℕ → Bool),
    BddAbove {n | probeAdmits J M ω n} := @bddAbove_probeAdmits
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    BddAbove {n | probeReaches J b M ω n} := @bddAbove_probeReaches
example : ∀ (J M : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ),
    n ≤ probeHorizon J M ω ↔ probeAdmits J M ω n := @le_probeHorizon_iff
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ),
    n ≤ probeCompleted J b M ω ↔ probeReaches J b M ω n := @le_probeCompleted_iff
example : ∀ (J M : ℕ) (ω : ℕ → ℕ → Bool),
    probeAdmits J M ω (probeHorizon J M ω) := @probeHorizon_admits
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeReaches J b M ω (probeCompleted J b M ω) := @probeCompleted_reaches
example : ∀ (J M : ℕ) (ω : ℕ → ℕ → Bool),
    probeHorizon J M ω ≤ M := @probeHorizon_le
example : ∀ {J M : ℕ} {ω : ℕ → ℕ → Bool} (h : probeHorizon J M ω < M),
    0 < probeHorizon J M ω ∧ tailUnresolved J (ω (probeHorizon J M ω - 1)) := @probeHorizon_unresolved
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeCompleted J b M ω ≤ probeHorizon J M ω := @probeCompleted_le_horizon
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeCompleted J b M ω ≤ M := @probeCompleted_le_cap
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeWork J ω (probeCompleted J b M ω) ≤ b := @probeWork_completed_le
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeCompleted J b M ω ≤ b := @probeCompleted_le_budget
example : ∀ (J : ℕ) (ω : ℕ → ℕ → Bool) {b b' M M' : ℕ} (hb : b ≤ b') (hM : M ≤ M'),
    probeCompleted J b M ω ≤ probeCompleted J b' M' ω := @probeCompleted_mono
example : ∀ (J : ℕ) (ω : ℕ → ℕ → Bool) {b M : ℕ} (h : b ≤ M),
    probeCompleted J b M ω = probeCompleted J b b ω := @probeCompleted_cap_inactive
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeFlips J b M ω ≤ b := @probeFlips_le
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeFlips J b M ω ≤ M * 4 ^ J := @probeFlips_le_cap
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeWork J ω (probeCompleted J b M ω) ≤ probeFlips J b M ω := @probeWork_completed_le_flips
example : ∀ {J b M : ℕ} {ω : ℕ → ℕ → Bool} (h : probeCompleted J b M ω = probeHorizon J M ω),
    probeFlips J b M ω = probeWork J ω (probeCompleted J b M ω) := @probeFlips_of_stopped
example : ∀ {J b M : ℕ} {ω : ℕ → ℕ → Bool} (h : probeCompleted J b M ω < probeHorizon J M ω),
    probeFlips J b M ω = b ∧ b < probeWork J ω (probeCompleted J b M ω + 1) := @probeFlips_of_running
example : ∀ (J M : ℕ) (ω : ℕ → ℕ → Bool) {b b' : ℕ} (h : b ≤ b'),
    probeFlips J b M ω ≤ probeFlips J b' M ω := @probeFlips_mono
example : ∀ {J b M : ℕ} {ω ω' : ℕ → ℕ → Bool} (h : ∀ i k, k < tailWork J (ω i) → probeWork J ω i + k < probeFlips J b M ω → ω i k = ω' i k),
    probeCompleted J b M ω' = probeCompleted J b M ω ∧
      probeFlips J b M ω' = probeFlips J b M ω ∧
      (probeUnresolved J b M ω' ↔ probeUnresolved J b M ω) := @probe_congr
example :
    probeUpper 0 = 1 := @probeUpper_zero
example : ∀ (n : ℕ),
    0 < probeUpper n := @probeUpper_pos
example : ∀ (n : ℕ),
    probeUpper n ≤ 1 := @probeUpper_le_one
example : ∀ {n : ℕ} (h : 0 < n),
    probeUpper n ≤ 8 / n := @probeUpper_le_div
example : ∀ {n n' : ℕ} (h : n ≤ n'),
    probeUpper n' ≤ probeUpper n := @probeUpper_antitone
example : ∀ (J n : ℕ),
    Measurable (fun ω : ℕ → ℕ → Bool => probeWork J ω n) := @measurable_probeWork
example : ∀ (J i : ℕ),
    Measurable (fun ω : ℕ → ℕ → Bool => tailUnresolved J (ω i)) := @measurable_streamUnresolved
example : ∀ (J M n : ℕ),
    MeasurableSet {ω : ℕ → ℕ → Bool | probeAdmits J M ω n} := @measurableSet_probeAdmits
example : ∀ (J b M n : ℕ),
    MeasurableSet {ω : ℕ → ℕ → Bool | probeReaches J b M ω n} := @measurableSet_probeReaches
example : ∀ (J b M : ℕ),
    Measurable (probeCompleted J b M) := @measurable_probeCompleted
example : ∀ (J : ℕ) (F : ℝ),
    MeasurableSet {ω : ℕ → ℕ → Bool | ∀ b M, F ≤ probeUpper (probeCompleted J b M ω)} := @measurableSet_probeValid
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (i : ℕ) {S : Set (ℕ → Bool)} (hS : MeasurableSet S),
    (Measure.infinitePi (fun _ : ℕ => ν)).real {ω | ω i ∈ S} = ν.real S := @stream_eval_real
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (i : ℕ) (G : (ℕ → Bool) → ℝ) (hG : Measurable G),
    ∫ ω, G (ω i) ∂Measure.infinitePi (fun _ : ℕ => ν) = ∫ t, G t ∂ν := @stream_eval_integral
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (J m : ℕ),
    (Measure.infinitePi (fun _ : ℕ => ν)).real {ω | ∀ i < m, ¬ tailUnresolved J (ω i)} =
      (1 - ν.real {t | tailUnresolved J t}) ^ m := @stream_all_resolved
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (J q : ℕ),
    (Measure.infinitePi (fun _ : ℕ => ν)).real {ω | ∃ i < q, tailUnresolved J (ω i)} ≤
      q * ν.real {t | tailUnresolved J t} := @stream_some_unresolved_le
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (J q : ℕ),
    Integrable (fun ω : ℕ → ℕ → Bool => (probeWork J ω q : ℝ))
      (Measure.infinitePi (fun _ : ℕ => ν)) := @integrable_probeWork
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (J q : ℕ),
    ∫ ω, (probeWork J ω q : ℝ) ∂Measure.infinitePi (fun _ : ℕ => ν) =
      q * ∫ t, (tailWork J t : ℝ) ∂ν := @stream_expected_work
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (J q b : ℕ) (hb : 0 < b),
    (Measure.infinitePi (fun _ : ℕ => ν)).real {ω | b < probeWork J ω q} ≤
      q * (∫ t, (tailWork J t : ℝ) ∂ν) / b := @stream_work_exceeds_le
example : ∀ {J b M : ℕ} {ω : ℕ → ℕ → Bool} {F u : ℝ} (hF1 : F ≤ 1) (hFu : F ≤ 2 * u) (h : probeUpper (probeCompleted J b M ω) < F),
    0 < u ∧ ∀ i < ⌊4 / u⌋₊, ¬ tailUnresolved J (ω i) := @resolved_prefix_of_upper_lt
example :
    exp (-3) ≤ 1 / 8 := @exp_neg_three_le
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (J : ℕ) {F : ℝ} (hF1 : F ≤ 1) (hFu : F ≤ 2 * ν.real {t | tailUnresolved J t}),
    (Measure.infinitePi (fun _ : ℕ => ν)).real
      {ω | ∃ b M, probeUpper (probeCompleted J b M ω) < F} ≤ 1 / 8 := @stream_probe_invalid_le
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (J : ℕ) {F : ℝ} (hF1 : F ≤ 1) (hFu : F ≤ 2 * ν.real {t | tailUnresolved J t}),
    7 / 8 ≤ (Measure.infinitePi (fun _ : ℕ => ν)).real
      {ω | ∀ b M, F ≤ probeUpper (probeCompleted J b M ω)} := @stream_probe_valid
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (J b M : ℕ) (hb : 0 < b) (hM : 0 < M) {W : ℝ} (hW : ∫ t, (tailWork J t : ℝ) ∂ν ≤ W),
    3 / 4 ≤ (Measure.infinitePi (fun _ : ℕ => ν)).real
      {ω | probeUpper (probeCompleted J b M ω) ≤
      min 1 (128 * max (max (ν.real {t | tailUnresolved J t}) (W / b)) (1 / M))} := @stream_probe_performance
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw),
    (originalSimulationLaw μ A q).map Prod.snd =
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q) := @originalSimulationLaw_coins
example : ∀ (J : ℕ) (d : Gap),
    1 ≤ tailWorkEnvelope J d := @one_le_tailWorkEnvelope
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (J : ℕ),
    1 ≤ ∫ d : Gap, tailWorkEnvelope J d ∂μ := @one_le_tailWorkEnvelope_integral
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J : ℕ),
    7 / 8 ≤ (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | ∀ b M, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      probeUpper (probeCompleted J b M ω)} := @original_probe_valid
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J b M : ℕ) (hb : 0 < b) (hM : 0 < M),
    3 / 4 ≤ (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | probeUpper (probeCompleted J b M ω) ≤
      min 1 (128 * max (max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M))} := @original_probe_performance
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J b M : ℕ) (hb : 0 < b) (hbM : b ≤ M),
    3 / 4 ≤ (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | probeUpper (probeCompleted J b M ω) ≤
      min 1 (128 * max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b))} := @original_probe_performance_uncapped
#print axioms ThresholdHC.ArbitraryLawAdaptation.bddAbove_probeAdmits
#print axioms ThresholdHC.ArbitraryLawAdaptation.bddAbove_probeReaches
#print axioms ThresholdHC.ArbitraryLawAdaptation.exp_neg_three_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.integrable_probeWork
#print axioms ThresholdHC.ArbitraryLawAdaptation.le_probeCompleted_iff
#print axioms ThresholdHC.ArbitraryLawAdaptation.le_probeHorizon_iff
#print axioms ThresholdHC.ArbitraryLawAdaptation.le_probeWork
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurableSet_probeAdmits
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurableSet_probeReaches
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurableSet_probeValid
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurable_probeCompleted
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurable_probeWork
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurable_streamUnresolved
#print axioms ThresholdHC.ArbitraryLawAdaptation.one_le_tailWorkEnvelope
#print axioms ThresholdHC.ArbitraryLawAdaptation.one_le_tailWorkEnvelope_integral
#print axioms ThresholdHC.ArbitraryLawAdaptation.originalSimulationLaw_coins
#print axioms ThresholdHC.ArbitraryLawAdaptation.original_probe_performance
#print axioms ThresholdHC.ArbitraryLawAdaptation.original_probe_performance_uncapped
#print axioms ThresholdHC.ArbitraryLawAdaptation.original_probe_valid
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeAdmits
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeAdmits_of_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeAdmits_zero
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeCompleted
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeCompleted_cap_inactive
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeCompleted_le_budget
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeCompleted_le_cap
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeCompleted_le_horizon
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeCompleted_mono
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeCompleted_reaches
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeFlips
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeFlips_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeFlips_le_cap
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeFlips_mono
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeFlips_of_running
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeFlips_of_stopped
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeHorizon
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeHorizon_admits
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeHorizon_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeHorizon_unresolved
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeReaches
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeReaches_of_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeReaches_zero
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeUnresolved
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeUpper
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeUpper_antitone
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeUpper_le_div
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeUpper_le_one
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeUpper_pos
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeUpper_zero
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeWork
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeWork_completed_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeWork_completed_le_flips
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeWork_congr
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeWork_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeWork_mono
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeWork_strictMono
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeWork_succ
#print axioms ThresholdHC.ArbitraryLawAdaptation.probeWork_zero
#print axioms ThresholdHC.ArbitraryLawAdaptation.probe_congr
#print axioms ThresholdHC.ArbitraryLawAdaptation.resolved_prefix_of_upper_lt
#print axioms ThresholdHC.ArbitraryLawAdaptation.stream_all_resolved
#print axioms ThresholdHC.ArbitraryLawAdaptation.stream_eval_integral
#print axioms ThresholdHC.ArbitraryLawAdaptation.stream_eval_real
#print axioms ThresholdHC.ArbitraryLawAdaptation.stream_expected_work
#print axioms ThresholdHC.ArbitraryLawAdaptation.stream_probe_invalid_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.stream_probe_performance
#print axioms ThresholdHC.ArbitraryLawAdaptation.stream_probe_valid
#print axioms ThresholdHC.ArbitraryLawAdaptation.stream_some_unresolved_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.stream_work_exceeds_le
