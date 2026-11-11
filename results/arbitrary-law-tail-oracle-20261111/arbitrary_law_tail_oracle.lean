
import ThresholdHC.ArbitraryLawAdaptation.TailOracleLaw
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Real ProbabilityTheory
open scoped ENNReal
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.Tier2 ThresholdHC.Tier6
open ThresholdHC.Uniform713 ThresholdHC.EntropyTailUpper ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.EntropyTailQuantile

example : ∀ (J : ℕ) (d : Gap), tailOracleKernel J d =
    tailUnresolvedProb J d + tailWorkEnvelope J d / 4 ^ J := fun _ _ => rfl
example : ∀ (μ : Measure Gap) (ρ : ℝ) (J : ℕ), TailOnset μ ρ J ↔
    2048 * ((J : ℝ) + 1) * (1 / 2) ^ J / (quantileThreshold μ ρ) ^ 2 ≤ Real.sqrt ρ :=
  fun _ _ _ => Iff.rfl

example : ∀ (J : ℕ),
    (1 / 2 : ℝ) ^ J = 1 / 2 ^ J := @half_pow_eq
example : ∀ (J : ℕ),
    (4 : ℝ) ^ J = (2 ^ J) ^ 2 := @four_pow_eq
example : ∀ {x : ℝ} (hx : 1 ≤ x),
    1 + Real.logb 2 x ≤ 2 * x := @one_add_logb_two_le
example : ∀ (J : ℕ) (d : Gap),
    tailWorkEnvelope J d / 4 ^ J ≤ 2048 * min 1 ((1 / 2) ^ J / (d : ℝ)) := @tailWorkEnvelope_div_le
example : ∀ (J : ℕ) (d : Gap),
    tailUnresolvedProb J d ≤ 4 * min 1 ((1 / 2) ^ J / (d : ℝ)) := @tailUnresolvedProb_le_four_min
example : ∀ (J : ℕ) (d : Gap),
    tailOracleKernel J d ≤ 2052 * min 1 ((1 / 2) ^ J / (d : ℝ)) := @tailOracleKernel_le_tail
example : ∀ (J : ℕ) (d : Gap),
    tailLog J d ≤ J := @tailLog_le
example : ∀ (J : ℕ) {a : ℝ} (ha : 0 < a) (d : Gap) (had : a ≤ (d : ℝ)),
    tailOracleKernel J d ≤ (1024 * ((J : ℝ) + 1) + 16) * ((1 / 2) ^ J) ^ 2 / a ^ 2 := @tailOracleKernel_le_core
example : ∀ (J : ℕ) (d : Gap),
    0 ≤ tailOracleKernel J d := @tailOracleKernel_nonneg
example : ∀ (J : ℕ) (d : Gap),
    tailOracleKernel J d ≤ 2 := @tailOracleKernel_le_two
example : ∀ (J : ℕ),
    Measurable (tailOracleKernel J) := @measurable_tailOracleKernel
example : ∀ (ξ : Measure Gap) [IsFiniteMeasure ξ] (J : ℕ),
    Integrable (tailOracleKernel J) ξ := @integrable_tailOracleKernel
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (J : ℕ),
    tailUnresolvedMass μ J + (∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J =
      ∫ d, tailOracleKernel J d ∂μ := @tail_oracle_integral
example : ∀ {a ρ : ℝ} (ha : 0 < a) (hρ : 0 < ρ),
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      2048 * ((J : ℝ) + 1) * (1 / 2) ^ J / a ^ 2 ≤ Real.sqrt ρ := @tail_onset_exists
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1),
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → TailOnset μ ρ J := @tailOnset_eventually
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (J : ℕ) (hsmall : 2 * (1 / 2 : ℝ) ^ J ≤ Real.sqrt ρ),
    ENNReal.ofReal (2 * (1 / 2) ^ J * Real.sqrt ρ) ≤ ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) := @selection_ge_scale
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (J : ℕ) (hon : TailOnset μ ρ J),
    ENNReal.ofReal (tailUnresolvedMass μ J + (∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J) ≤
      4096 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) := @tail_oracle_comparison
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (J : ℕ) (hon : TailOnset μ ρ J),
    ENNReal.ofReal (min 1 (128 * max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J))) ≤
      524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) := @tail_bound_le_oracle
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (J m : ℕ) (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) (hmδ : 8 * log (2 / δ) ≤ m) (hon : TailOnset μ ρ J),
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))).real
      {ω | (∀ b' M' : ℕ → ℕ,
      μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J m b' M' ω) ∧
      ENNReal.ofReal (medianUpper J m (fun _ => 4 ^ J) (fun _ => 4 ^ J) ω) ≤
      524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)} := @original_tail_oracle
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (J m : ℕ) (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) (hmδ : 8 * log (2 / δ) ≤ m) (hon : TailOnset μ ρ J),
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      medianUpper J m b' M' (fun j i => ω (Nat.pair j i))) ∧
      ENNReal.ofReal (medianUpper J m (fun _ => 4 ^ J) (fun _ => 4 ^ J)
      (fun j i => ω (Nat.pair j i))) ≤
      524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)} := @original_tail_oracle_array
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4),
    ∃ J₀ : ℕ, ∀ (J m : ℕ) (δ : ℝ), J₀ ≤ J → 0 < m → 0 < δ → 8 * log (2 / δ) ≤ m →
      1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      medianUpper J m b' M' (fun j i => ω (Nat.pair j i))) ∧
      ENNReal.ofReal (medianUpper J m (fun _ => 4 ^ J) (fun _ => 4 ^ J)
      (fun j i => ω (Nat.pair j i))) ≤
      524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)} := @original_tail_oracle_eventually
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (m : ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ) (hm : ∀ J : ℕ, 1 ≤ J → 0 < m J) (hmδ : ∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J),
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))).real
      {ω | ∀ J, 1 ≤ J →
      (∀ b' M' : ℕ → ℕ,
      μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J (m J) b' M' (ω J)) ∧
      (TailOnset μ ρ J →
      ENNReal.ofReal (medianUpper J (m J) (fun _ => 4 ^ J) (fun _ => 4 ^ J) (ω J)) ≤
      524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J))} := @original_tail_oracle_all_depths
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (m : ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ) (hm : ∀ J : ℕ, 1 ≤ J → 0 < m J) (hmδ : ∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J),
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | ∀ J, 1 ≤ J →
      (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      medianUpper J (m J) b' M' (fun j i => ω (Nat.pair J (Nat.pair j i)))) ∧
      (TailOnset μ ρ J →
      ENNReal.ofReal (medianUpper J (m J) (fun _ => 4 ^ J) (fun _ => 4 ^ J)
      (fun j i => ω (Nat.pair J (Nat.pair j i)))) ≤
      524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J))} := @original_tail_oracle_all_depths_array
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4),
    ∃ J₀ : ℕ, ∀ (m : ℕ → ℕ) (δ : ℝ), 0 < δ → (∀ J : ℕ, 1 ≤ J → 0 < m J) →
      (∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J) →
      1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | ∀ J, 1 ≤ J →
      (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      medianUpper J (m J) b' M' (fun j i => ω (Nat.pair J (Nat.pair j i)))) ∧
      (J₀ ≤ J →
      ENNReal.ofReal (medianUpper J (m J) (fun _ => 4 ^ J) (fun _ => 4 ^ J)
      (fun j i => ω (Nat.pair J (Nat.pair j i)))) ≤
      524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J))} := @original_tail_oracle_all_depths_eventually
#print axioms ThresholdHC.ArbitraryLawAdaptation.TailOnset
#print axioms ThresholdHC.ArbitraryLawAdaptation.four_pow_eq
#print axioms ThresholdHC.ArbitraryLawAdaptation.half_pow_eq
#print axioms ThresholdHC.ArbitraryLawAdaptation.integrable_tailOracleKernel
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurable_tailOracleKernel
#print axioms ThresholdHC.ArbitraryLawAdaptation.one_add_logb_two_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.original_tail_oracle
#print axioms ThresholdHC.ArbitraryLawAdaptation.original_tail_oracle_all_depths
#print axioms ThresholdHC.ArbitraryLawAdaptation.original_tail_oracle_all_depths_array
#print axioms ThresholdHC.ArbitraryLawAdaptation.original_tail_oracle_all_depths_eventually
#print axioms ThresholdHC.ArbitraryLawAdaptation.original_tail_oracle_array
#print axioms ThresholdHC.ArbitraryLawAdaptation.original_tail_oracle_eventually
#print axioms ThresholdHC.ArbitraryLawAdaptation.selection_ge_scale
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailLog_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailOnset_eventually
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailOracleKernel
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailOracleKernel_le_core
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailOracleKernel_le_tail
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailOracleKernel_le_two
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailOracleKernel_nonneg
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailUnresolvedProb_le_four_min
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailWorkEnvelope_div_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.tail_bound_le_oracle
#print axioms ThresholdHC.ArbitraryLawAdaptation.tail_onset_exists
#print axioms ThresholdHC.ArbitraryLawAdaptation.tail_oracle_comparison
#print axioms ThresholdHC.ArbitraryLawAdaptation.tail_oracle_integral
