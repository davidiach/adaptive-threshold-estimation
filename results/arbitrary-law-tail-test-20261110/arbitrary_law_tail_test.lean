
import ThresholdHC.ArbitraryLawAdaptation.TailTestLaw
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Real ProbabilityTheory
open scoped ENNReal
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.Tier2 ThresholdHC.Tier6
open ThresholdHC.Uniform713 ThresholdHC.EntropyTailUpper ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation

example : ∀ (n : ℕ) (ω : ℕ → Bool), tailHeads n ω = ∑ i ∈ Finset.range n, (ω i).toNat :=
  fun _ _ => rfl
example : ∀ J k : ℕ, tailScale J k = 2 * 4 ^ k * (J - k + 2) := fun _ _ => rfl
example : ∀ J k : ℕ, tailThreshold J k = ⌈Real.sqrt (tailScale J k)⌉₊ := fun _ _ => rfl
example : ∀ (J k : ℕ) (ω : ℕ → Bool), tailResolvedAt J k ω ↔
    2 * (tailThreshold J k : ℤ) < |2 * (tailHeads (4 ^ k) ω : ℤ) - ((4 ^ k : ℕ) : ℤ)| :=
  fun _ _ _ => Iff.rfl
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    tailUnresolved J ω ↔ ∀ k, k ≤ J → ¬ tailResolvedAt J k ω := fun _ _ => Iff.rfl
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    tailStop J ω = sInf {k | J ≤ k ∨ tailResolvedAt J k ω} := fun _ _ => rfl
example : ∀ (J : ℕ) (ω : ℕ → Bool), tailWork J ω = 4 ^ tailStop J ω := fun _ _ => rfl
example : ∀ (ω : ℕ → Bool) (i : ℕ), tapeFlip ω i = !ω i := fun _ _ => rfl
example : ∀ (J : ℕ) (d : ℝ), tailLog J d = max 0 (Real.logb 2 (d * 2 ^ J)) := fun _ _ => rfl
example : ∀ (J : ℕ) (d : ℝ),
    tailWorkEnvelope J d = min (4 ^ J) (1024 / d ^ 2 * (1 + tailLog J d)) := fun _ _ => rfl
example : ∀ (J : ℕ) (d : Gap), tailUnresolvedProb J d =
    (tapeMeasure (gapParameter true d)).real {ω | tailUnresolved J ω} := fun _ _ => rfl
example : ∀ (μ : Measure Gap) (J : ℕ),
    tailUnresolvedMass μ J = ∫ d, tailUnresolvedProb J d ∂μ := fun _ _ => rfl

example : ∀ (n : ℕ) (ω : ℕ → Bool),
    tailHeads n ω ≤ n := @tailHeads_le
example : ∀ {n : ℕ} {ω ω' : ℕ → Bool} (h : ∀ i < n, ω i = ω' i),
    tailHeads n ω = tailHeads n ω' := @tailHeads_congr
example : ∀ (n : ℕ) (ω : ℕ → Bool),
    tailHeads n (tapeFlip ω) = n - tailHeads n ω := @tailHeads_flip
example : ∀ (n : ℕ) (ω : ℕ → Bool),
    prefixMean observations n ω = (tailHeads n ω : ℝ) / n := @prefixMean_eq_heads
example : ∀ (J k : ℕ),
    (tailScale J k : ℝ) ≤ (tailThreshold J k : ℝ) ^ 2 := @tailScale_le_threshold_sq
example : ∀ (J k : ℕ),
    (tailThreshold J k : ℝ) < Real.sqrt (tailScale J k) + 1 := @tailThreshold_lt
example : ∀ (J k a : ℕ),
    tailThreshold J k ≤ a ↔ tailScale J k ≤ a ^ 2 := @tailThreshold_le_iff
example : ∀ (J : ℕ),
    tailThreshold J J = 2 ^ (J + 1) := @tailThreshold_terminal
example : ∀ (J k : ℕ) (ω : ℕ → Bool),
    tailResolvedAt J k ω ↔
      (tailThreshold J k : ℝ) / 4 ^ k < |prefixMean observations (4 ^ k) ω - 1 / 2| := @tailResolvedAt_iff
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    tailStop J ω ≤ J := @tailStop_le
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    J ≤ tailStop J ω ∨ tailResolvedAt J (tailStop J ω) ω := @tailStop_mem
example : ∀ {J k : ℕ} {ω : ℕ → Bool} (h : k < tailStop J ω),
    ¬ tailResolvedAt J k ω := @not_resolved_of_lt_stop
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    1 ≤ tailWork J ω := @tailWork_pos
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    tailWork J ω ≤ 4 ^ J := @tailWork_le
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    tailUnresolved J ω ↔ ¬ tailResolvedAt J (tailStop J ω) ω := @tailUnresolved_iff
example : ∀ {J k : ℕ} {ω ω' : ℕ → Bool} (h : ∀ i < 4 ^ k, ω i = ω' i),
    tailResolvedAt J k ω ↔ tailResolvedAt J k ω' := @tailResolvedAt_congr
example : ∀ {J : ℕ} {ω ω' : ℕ → Bool} (h : ∀ i < tailWork J ω, ω i = ω' i),
    tailStop J ω' = tailStop J ω := @tailStop_congr
example : ∀ {J : ℕ} {ω ω' : ℕ → Bool} (h : ∀ i < tailWork J ω, ω i = ω' i),
    tailWork J ω' = tailWork J ω := @tailWork_congr
example : ∀ {J : ℕ} {ω ω' : ℕ → Bool} (h : ∀ i < tailWork J ω, ω i = ω' i),
    tailUnresolved J ω' ↔ tailUnresolved J ω := @tailUnresolved_congr
example : ∀ (J k : ℕ) (ω : ℕ → Bool),
    tailResolvedAt J k (tapeFlip ω) ↔ tailResolvedAt J k ω := @tailResolvedAt_flip
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    tailStop J (tapeFlip ω) = tailStop J ω := @tailStop_flip
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    tailWork J (tapeFlip ω) = tailWork J ω := @tailWork_flip
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    tailUnresolved J (tapeFlip ω) ↔ tailUnresolved J ω := @tailUnresolved_flip
example : ∀ {α : Type*} [MeasurableSpace α] (M : ℕ) (f : (ℕ → Bool) → α) (h : ∀ ω ω', (∀ i < M, ω i = ω' i) → f ω = f ω'),
    Measurable f := @measurable_of_tape_prefix
example : ∀ (n : ℕ),
    Measurable (tailHeads n) := @measurable_tailHeads
example : ∀ (J : ℕ),
    Measurable (tailStop J) := @measurable_tailStop
example : ∀ (J : ℕ),
    Measurable (tailWork J) := @measurable_tailWork
example : Measurable tapeFlip := measurable_tapeFlip
example : ∀ (J k : ℕ),
    MeasurableSet {ω | tailResolvedAt J k ω} := @measurableSet_tailResolvedAt
example : ∀ (J : ℕ),
    MeasurableSet {ω | tailUnresolved J ω} := @measurableSet_tailUnresolved
example : ∀ (d : Gap),
    ((gapParameter true d : unitInterval) : ℝ) = 1 / 2 + (d : ℝ) := @gapParameter_true_coe
example : exp (-1) ≤ 10 / 27 := exp_neg_one_le
example : ∀ (m : ℕ),
    exp (-(m : ℝ)) ≤ (10 / 27) ^ m := @exp_neg_nat_le
example : ∀ (J : ℕ),
    ∑ k ∈ Finset.range (J + 1), ((10 : ℝ) / 27) ^ (J - k) ≤ 27 / 17 := @tail_geometric_sum
example : ∀ (J k : ℕ),
    2 * (2 : ℝ) ^ k ≤ (tailThreshold J k : ℝ) := @tailThreshold_ge
example : ∀ (J k : ℕ),
    (tailScale J k : ℝ) = 2 * 4 ^ k * ((J - k + 2 : ℕ) : ℝ) := @tailScale_cast
example : ∀ (J k : ℕ) (d : Gap) (hr : 2 * (tailThreshold J k : ℝ) ≤ 4 ^ k * (d : ℝ)),
    (tapeMeasure (gapParameter true d)).real {ω | ¬ tailResolvedAt J k ω} ≤
      exp (-(4 ^ k * (d : ℝ) ^ 2 / 2)) := @tail_not_resolved_le_exp
example : ∀ (J k : ℕ) (d : Gap) (hd : 2 * (4 ^ k * (d : ℝ)) ≤ (tailThreshold J k : ℝ)),
    (tapeMeasure (gapParameter true d)).real {ω | tailResolvedAt J k ω} ≤
      2 * exp (-((tailThreshold J k : ℝ) ^ 2 / (2 * 4 ^ k))) := @tail_resolved_le_exp
example : ∀ (J k : ℕ) (hk : k ≤ J) (d : Gap) (hd : (d : ℝ) ≤ (1 / 2) ^ J),
    (tapeMeasure (gapParameter true d)).real {ω | tailResolvedAt J k ω} ≤
      2 * (10 / 27 : ℝ) ^ (J - k + 2) := @tail_resolved_small_gap
example : ∀ (J : ℕ) (d : Gap) (hd : (d : ℝ) ≤ (1 / 2) ^ J),
    1 / 2 ≤ (tapeMeasure (gapParameter true d)).real {ω | tailUnresolved J ω} := @tail_unresolved_ge_half
example : ∀ (J : ℕ) (d : Gap) (hd : 4 * (1 / 2 : ℝ) ^ J ≤ (d : ℝ)),
    (tapeMeasure (gapParameter true d)).real {ω | tailUnresolved J ω} ≤
      exp (-(4 ^ J * (d : ℝ) ^ 2 / 2)) := @tail_unresolved_le_exp
example : ∀ (J k : ℕ) {d : ℝ} (hd : 0 ≤ d) (hC : 36 * ((J - k + 2 : ℕ) : ℝ) ≤ 4 ^ k * d ^ 2),
    2 * (tailThreshold J k : ℝ) ≤ 4 ^ k * d := @tailThreshold_le_of_scale
example : ∀ (k0 j : ℕ) {d : ℝ} (hk0 : 72 ≤ 4 ^ k0 * d ^ 2),
    3 * (4 : ℝ) ^ (k0 + j) * exp (-(4 ^ (k0 + j) * d ^ 2 / 2)) ≤ 4 ^ k0 * (1 / 2) ^ j / 2 := @tail_work_term
example : ∀ (J s : ℕ) (hs : s ≤ J),
    (4 : ℝ) ^ s = 1 + ∑ k ∈ Finset.range J, 3 * 4 ^ k * (if k < s then (1 : ℝ) else 0) := @four_pow_layer
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    (tailWork J ω : ℝ) =
      1 + ∑ k ∈ Finset.range J, 3 * 4 ^ k * (if k < tailStop J ω then (1 : ℝ) else 0) := @tailWork_sum
example : ∀ (J : ℕ) (P : Measure (ℕ → Bool)) [IsFiniteMeasure P],
    Integrable (fun ω => (tailWork J ω : ℝ)) P := @integrable_tailWork
example : ∀ (J k : ℕ),
    MeasurableSet {ω | k < tailStop J ω} := @measurableSet_stop_gt
example : ∀ (J : ℕ) (P : Measure (ℕ → Bool)) [IsProbabilityMeasure P],
    ∫ ω, (tailWork J ω : ℝ) ∂P =
      1 + ∑ k ∈ Finset.range J, 3 * 4 ^ k * P.real {ω | k < tailStop J ω} := @tail_expected_work_eq
example : ∀ (J : ℕ) (d : Gap),
    ∫ ω, (tailWork J ω : ℝ) ∂tapeMeasure (gapParameter true d) ≤ tailWorkEnvelope J d := @tail_expected_work_le
example : ∀ (p : unitInterval),
    (tapeMeasure p).map tapeFlip = tapeMeasure (unitInterval.symm p) := @tapeMeasure_flip
example : ∀ (d : Gap),
    gapParameter false d = unitInterval.symm (gapParameter true d) := @gapParameter_false_eq
example : ∀ (d : Gap) {S : Set (ℕ → Bool)} (hS : MeasurableSet S) (hflip : tapeFlip ⁻¹' S = S),
    tapeMeasure (gapParameter false d) S = tapeMeasure (gapParameter true d) S := @tapeMeasure_flip_invariant
example : ∀ (p : unitInterval) (G : (ℕ → Bool) → ℝ) (hG : Measurable G) (hflip : ∀ t, G (tapeFlip t) = G t),
    ∫ t, G t ∂tapeMeasure (unitInterval.symm p) = ∫ t, G t ∂tapeMeasure p := @tape_integral_flip
example : ∀ (J : ℕ) (d : Gap),
    (tapeMeasure (gapParameter false d)).map (tailStop J) =
      (tapeMeasure (gapParameter true d)).map (tailStop J) := @tailStop_law_sign_neutral
example : ∀ (J : ℕ),
    tapeFlip ⁻¹' {ω | tailUnresolved J ω} = {ω | tailUnresolved J ω} := @tailUnresolved_flip_preimage
example : ∀ (J : ℕ) (d : Gap),
    tapeMeasure (gapParameter false d) {ω | tailUnresolved J ω} =
      tapeMeasure (gapParameter true d) {ω | tailUnresolved J ω} := @tailUnresolved_sign_neutral
example : ∀ (κ : Measure unitInterval) [IsProbabilityMeasure κ] (F : (ℕ → Bool) → ℝ) (hF : Measurable F) {M : ℝ} (hb : ∀ t, |F t| ≤ M),
    (∫ t, F t ∂parameterTapeLaw κ) = ∫ p, (∫ t, F t ∂tapeMeasure p) ∂κ := @parameterTape_integral
example : ∀ (F : (ℕ → Bool) → ℝ) (hF : Measurable F),
    Measurable (fun p : unitInterval => ∫ t, F t ∂tapeMeasure p) := @measurable_tape_integral
example : ∀ (p : unitInterval) (G : (ℕ → Bool) → ℝ) {M : ℝ} (hb : ∀ t, |G t| ≤ M),
    |∫ t, G t ∂tapeMeasure p| ≤ M := @tape_integral_abs_le
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (G : (ℕ → Bool) → ℝ) (hG : Measurable G) {M : ℝ} (hb : ∀ t, |G t| ≤ M) (hflip : ∀ t, G (tapeFlip t) = G t),
    ∫ t, G t ∂originalPopulationTapeLaw μ q =
      ∫ d, (∫ t, G t ∂tapeMeasure (gapParameter true d)) ∂μ := @original_tape_integral_sign_neutral
example : ∀ (J : ℕ) (d : Gap),
    tailUnresolvedProb J d = ∫ t, Set.indicator {ω | tailUnresolved J ω} (fun _ => (1 : ℝ)) t
      ∂tapeMeasure (gapParameter true d) := @tailUnresolvedProb_eq_integral
example : ∀ (J : ℕ),
    Measurable (tailUnresolvedProb J) := @measurable_tailUnresolvedProb
example : ∀ (J : ℕ) (d : Gap),
    0 ≤ tailUnresolvedProb J d := @tailUnresolvedProb_nonneg
example : ∀ (J : ℕ) (d : Gap),
    tailUnresolvedProb J d ≤ 1 := @tailUnresolvedProb_le_one
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (J : ℕ),
    Integrable (tailUnresolvedProb J) μ := @integrable_tailUnresolvedProb
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J : ℕ),
    (originalPopulationTapeLaw μ q).real {ω | tailUnresolved J ω} = tailUnresolvedMass μ J := @original_tail_unresolved
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (J : ℕ),
    μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} / 2 ≤ tailUnresolvedMass μ J := @tail_unresolved_mass_lower
example : ∀ (J : ℕ) (d : Gap) (hd : 4 * (1 / 2 : ℝ) ^ J ≤ (d : ℝ)),
    tailUnresolvedProb J d ≤ exp (-(4 ^ J * (d : ℝ) ^ 2 / 2)) := @tailUnresolvedProb_le_exp
example : ∀ (J : ℕ),
    (4 : ℝ) ^ J * ((1 / 2 : ℝ) ^ J) ^ 2 = 1 := @four_pow_half_pow
example : ∀ (J : ℕ) (d : Gap),
    tailUnresolvedProb J d ≤ min 1 (16 * ((1 / 2) ^ J / (d : ℝ)) ^ 2) := @tailUnresolvedProb_le_envelope
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (J : ℕ),
    tailUnresolvedMass μ J ≤ ∫ d : Gap, min 1 (16 * ((1 / 2) ^ J / (d : ℝ)) ^ 2) ∂μ := @tail_unresolved_mass_upper
example : ∀ (J : ℕ) (d : Gap),
    tailUnresolvedProb J d ≤ lightCDF ((1 / 2) ^ J / (d : ℝ)) := @tailUnresolvedProb_le_lightCDF
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (J : ℕ),
    ENNReal.ofReal (tailUnresolvedMass μ J) ≤
      (μ.prod lightMultiplier) {z : Gap × Gap | (z.1 : ℝ) * (z.2 : ℝ) ≤ (1 / 2) ^ J} := @tail_unresolved_mass_le_multiplier
example : ∀ (J : ℕ) (d : ℝ),
    0 ≤ tailLog J d := @tailLog_nonneg
example : ∀ (J : ℕ) (d : ℝ),
    tailWorkEnvelope J d ≤ 4 ^ J := @tailWorkEnvelope_le
example : ∀ (J : ℕ) (d : ℝ),
    0 ≤ tailWorkEnvelope J d := @tailWorkEnvelope_nonneg
example : ∀ (J : ℕ),
    Measurable (tailWorkEnvelope J) := @measurable_tailWorkEnvelope
example : ∀ (J : ℕ) (s : Bool) (d : Gap),
    ∫ ω, (tailWork J ω : ℝ) ∂tapeMeasure (gapParameter s d) ≤ tailWorkEnvelope J d := @tail_expected_work_le_sign
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J : ℕ),
    ∫ t, (tailWork J t : ℝ) ∂originalPopulationTapeLaw μ q ≤
      ∫ d : Gap, tailWorkEnvelope J d ∂μ := @original_tail_expected_work
#print axioms ThresholdHC.ArbitraryLawAdaptation.exp_neg_nat_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.exp_neg_one_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.four_pow_half_pow
#print axioms ThresholdHC.ArbitraryLawAdaptation.four_pow_layer
#print axioms ThresholdHC.ArbitraryLawAdaptation.gapParameter_false_eq
#print axioms ThresholdHC.ArbitraryLawAdaptation.gapParameter_true_coe
#print axioms ThresholdHC.ArbitraryLawAdaptation.integrable_tailUnresolvedProb
#print axioms ThresholdHC.ArbitraryLawAdaptation.integrable_tailWork
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurableSet_stop_gt
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurableSet_tailResolvedAt
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurableSet_tailUnresolved
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurable_of_tape_prefix
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurable_tailHeads
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurable_tailStop
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurable_tailUnresolvedProb
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurable_tailWork
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurable_tailWorkEnvelope
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurable_tapeFlip
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurable_tape_integral
#print axioms ThresholdHC.ArbitraryLawAdaptation.not_resolved_of_lt_stop
#print axioms ThresholdHC.ArbitraryLawAdaptation.original_tail_expected_work
#print axioms ThresholdHC.ArbitraryLawAdaptation.original_tail_unresolved
#print axioms ThresholdHC.ArbitraryLawAdaptation.original_tape_integral_sign_neutral
#print axioms ThresholdHC.ArbitraryLawAdaptation.parameterTape_integral
#print axioms ThresholdHC.ArbitraryLawAdaptation.prefixMean_eq_heads
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailHeads
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailHeads_congr
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailHeads_flip
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailHeads_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailLog
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailLog_nonneg
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailResolvedAt
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailResolvedAt_congr
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailResolvedAt_flip
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailResolvedAt_iff
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailScale
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailScale_cast
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailScale_le_threshold_sq
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailStop
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailStop_congr
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailStop_flip
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailStop_law_sign_neutral
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailStop_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailStop_mem
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailThreshold
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailThreshold_ge
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailThreshold_le_iff
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailThreshold_le_of_scale
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailThreshold_lt
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailThreshold_terminal
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailUnresolved
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailUnresolvedMass
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailUnresolvedProb
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailUnresolvedProb_eq_integral
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailUnresolvedProb_le_envelope
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailUnresolvedProb_le_exp
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailUnresolvedProb_le_lightCDF
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailUnresolvedProb_le_one
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailUnresolvedProb_nonneg
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailUnresolved_congr
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailUnresolved_flip
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailUnresolved_flip_preimage
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailUnresolved_iff
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailUnresolved_sign_neutral
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailWork
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailWorkEnvelope
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailWorkEnvelope_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailWorkEnvelope_nonneg
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailWork_congr
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailWork_flip
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailWork_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailWork_pos
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailWork_sum
#print axioms ThresholdHC.ArbitraryLawAdaptation.tail_expected_work_eq
#print axioms ThresholdHC.ArbitraryLawAdaptation.tail_expected_work_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.tail_expected_work_le_sign
#print axioms ThresholdHC.ArbitraryLawAdaptation.tail_geometric_sum
#print axioms ThresholdHC.ArbitraryLawAdaptation.tail_not_resolved_le_exp
#print axioms ThresholdHC.ArbitraryLawAdaptation.tail_resolved_le_exp
#print axioms ThresholdHC.ArbitraryLawAdaptation.tail_resolved_small_gap
#print axioms ThresholdHC.ArbitraryLawAdaptation.tail_unresolved_ge_half
#print axioms ThresholdHC.ArbitraryLawAdaptation.tail_unresolved_le_exp
#print axioms ThresholdHC.ArbitraryLawAdaptation.tail_unresolved_mass_le_multiplier
#print axioms ThresholdHC.ArbitraryLawAdaptation.tail_unresolved_mass_lower
#print axioms ThresholdHC.ArbitraryLawAdaptation.tail_unresolved_mass_upper
#print axioms ThresholdHC.ArbitraryLawAdaptation.tail_work_term
#print axioms ThresholdHC.ArbitraryLawAdaptation.tapeFlip
#print axioms ThresholdHC.ArbitraryLawAdaptation.tapeMeasure_flip
#print axioms ThresholdHC.ArbitraryLawAdaptation.tapeMeasure_flip_invariant
#print axioms ThresholdHC.ArbitraryLawAdaptation.tape_integral_abs_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.tape_integral_flip
