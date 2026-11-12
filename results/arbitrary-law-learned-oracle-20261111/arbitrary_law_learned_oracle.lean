
import ThresholdHC.ArbitraryLawAdaptation.LearnedOracle
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Real ProbabilityTheory
open scoped ENNReal
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.Tier2 ThresholdHC.Tier6
open ThresholdHC.CriticalEntropy ThresholdHC.EntropyTailQuantile
open ThresholdHC.ObservableSimulation

example : ∀ (μ : Measure Gap),
    lightLaw μ = (μ.prod lightMultiplier).map lightGap := fun _ => rfl
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    IsProbabilityMeasure (lightLaw μ) := @lightLaw_probability
example : ∀ (μ : Measure Gap) (ρ : ℝ) (J : ℕ),
    pilotWorkBound μ ρ J =
      8192 * tailModulus (quantileTail μ ρ) ((1 / 2) ^ J) +
        2048 * ((J : ℝ) + 1) ^ 3 * ((1 / 2) ^ J) ^ 2 / (quantileThreshold μ ρ) ^ 2 :=
  fun _ _ _ => rfl
example : ∀ (μ : Measure Gap) (ρ : ℝ) (J : ℕ) (c : ℝ),
    learnedSlack μ ρ J c =
      128 * pilotWorkBound μ ρ J + 128 / (pilotCoinCap J ρ : ℝ) + c := fun _ _ _ _ => rfl
example : ∀ (η : Measure Gap) (e : ℝ),
    clippedLaw η e =
      if 1 ≤ e then Measure.dirac 0
      else ENNReal.ofReal e • Measure.dirac 0 +
        (128 : ℝ≥0∞) • (quantileTail η ((1 - e) / 128)).map Subtype.val := fun _ _ => rfl
example : ∀ (μ : Measure Gap) (j : ℕ),
    lightLaw μ {y : Gap | (y : ℝ) ≤ (1 / 2) ^ (j + 1)} =
      (μ.prod lightMultiplier) {z : Gap × Gap | (z.1 : ℝ) * (z.2 : ℝ) ≤ (1 / 2) ^ j} := @lightLaw_apply_le
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (j : ℕ),
    tailUnresolvedMass μ j ≤ (lightLaw μ).real {y : Gap | (y : ℝ) ≤ (1 / 2) ^ (j + 1)} := @tailUnresolvedMass_le_light
example : ∀ {G : ℝ → ℝ} {c : ℕ → ℝ} (hG : Monotone G) (n : ℕ),
    ∀ x : ℝ, gridPoint (n + 1) ≤ x → (∀ j, j < n + 1 → c j ≤ G (gridPoint (j + 1))) →
      envelopeCDF c n x ≤ G x := @envelopeCDF_le_above
example : ∀ {G : ℝ → ℝ} {c : ℕ → ℝ} {n : ℕ} (hG : Monotone G) (hneg : ∀ x : ℝ, x < 0 → 0 ≤ G x) (hzero : c n ≤ G 0) (hgrid : ∀ j, j < n → c j ≤ G (gridPoint (j + 1))) (x : ℝ),
    envelopeCDF c n x ≤ G x := @envelopeCDF_le
example : ∀ (μ : Measure Gap) (ρ : ℝ) (J : ℕ),
    0 ≤ pilotWorkBound μ ρ J := @pilotWorkBound_nonneg
example : ∀ (μ : Measure Gap) (ρ : ℝ) (J : ℕ) (c : ℝ),
    c ≤ learnedSlack μ ρ J c := @le_learnedSlack
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {J j : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J),
    pilotBound μ J ρ j ≤
      128 * (lightLaw μ).real {y : Gap | (y : ℝ) ≤ (1 / 2) ^ (j + 1)} +
      128 * pilotWorkBound μ ρ J + 128 / (pilotCoinCap J ρ : ℝ) := @pilotBound_le_light
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {J : ℕ} (U : ℕ → ℝ) (hU0 : ∀ i, 0 ≤ U i) (hU1 : U 0 = 1) (hbound : ∀ i, i < J → U i ≤ pilotBound μ J ρ (i + 1)) (x : ℝ),
    envelopeLaw (prefixMinimum U) (J - 1) (Set.Iic x) ≤
      ENNReal.ofReal (min 1 (128 * (lightLaw μ).real {y : Gap | (y : ℝ) ≤ x} +
      learnedSlack μ ρ J (prefixMinimum U (J - 1)))) := @learned_cdf_le
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hon : PilotOnset μ ρ J),
    ENNReal.ofReal (pilotWorkBound μ ρ J) ≤ 8193 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) := @pilotWorkBound_le_oracle
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hJ : 1 ≤ J) (hon : PilotOnset μ ρ J) (U : ℕ → ℝ) (hbound : U (J - 1) ≤ pilotBound μ J ρ J),
    ENNReal.ofReal (learnedSlack μ ρ J (prefixMinimum U (J - 1))) ≤
      2621712 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) := @learnedSlack_le_explicit
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hJ : 1 ≤ J) (hon : PilotOnset μ ρ J) (U : ℕ → ℝ) (hbound : U (J - 1) ≤ pilotBound μ J ρ J),
    ENNReal.ofReal (learnedSlack μ ρ J (prefixMinimum U (J - 1))) ≤
      4194304 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) := @learnedSlack_le_oracle
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hon : PilotOnset μ ρ J),
    ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) ≠ ⊤ ∧
      0 < (ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)).toReal := @pilotOnset_selection_pos
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hJ : 1 ≤ J) (hon : PilotOnset μ ρ J) (U : ℕ → ℝ) (hbound : U (J - 1) ≤ pilotBound μ J ρ J),
    ENNReal.ofReal (learnedSlack μ ρ J (prefixMinimum U (J - 1))) <
      4194304 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) := @learnedSlack_lt_oracle
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (x : ℝ),
    (quantileTail η r).real {d : Gap | (d : ℝ) ≤ x} =
      min r (η.real {d : Gap | (d : ℝ) ≤ x}) := @quantileTail_cdf
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] {e : ℝ} (he : 0 ≤ e),
    clippedLaw η e ≤
      ENNReal.ofReal 128 • η.map Subtype.val + ENNReal.ofReal e • Measure.dirac 0 := @clippedLaw_le
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] {e : ℝ} (he : 0 ≤ e),
    IsProbabilityMeasure (clippedLaw η e) := @clippedLaw_probability
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] {e : ℝ} (he : 0 ≤ e) {x : ℝ} (hx : 0 ≤ x),
    clippedLaw η e (Set.Iic x) =
      ENNReal.ofReal (min 1 (128 * η.real {d : Gap | (d : ℝ) ≤ x} + e)) := @clippedLaw_Iic
example : ∀ (η : Measure Gap) (e : ℝ),
    clippedLaw η e (Set.Iio 0) = 0 := @clippedLaw_Iio_zero
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] {e : ℝ} (he : 0 ≤ e) {x : ℝ} (hx : 0 ≤ x),
    cdf (clippedLaw η e) x = min 1 (128 * η.real {d : Gap | (d : ℝ) ≤ x} + e) := @clippedLaw_cdf
example : ∀ (c : ℕ → ℝ) (n : ℕ) {x : ℝ} (hx : gridPoint 1 ≤ x),
    envelopeCDF c n x = c 0 := @envelopeCDF_top
example : ∀ (c : ℕ → ℝ) (n : ℕ),
    envelopeLaw c n (Set.Iio 0) = 0 := @envelopeLaw_Iio_zero
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hJ : 1 ≤ J) (hon : PilotOnset μ ρ J) (U : ℕ → ℝ) (hU0 : ∀ i, 0 ≤ U i) (hU1 : U 0 = 1) (hbound : ∀ i, i < J → U i ≤ pilotBound μ J ρ (i + 1)),
    zeroSelection (envelopeLaw (prefixMinimum U) (J - 1)) ρ (4 ^ J) ≤
      16777216 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) := @learned_selection_le
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4),
    ∃ J₀ : ℕ, 1 ≤ J₀ ∧ ∀ (J : ℕ) (U : ℕ → ℝ), J₀ ≤ J → (∀ i, 0 ≤ U i) → U 0 = 1 →
      (∀ i, i < J → U i ≤ pilotBound μ J ρ (i + 1)) →
      zeroSelection (envelopeLaw (prefixMinimum U) (J - 1)) ρ (4 ^ J) ≤
      16777216 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) := @learned_selection_eventually
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ] (S : LearnedStage R) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hJ : 1 ≤ J) (hon : PilotOnset μ ρ J) (m : ℕ) (xs : List Bool) (hbound : ∀ i, i < J → (pilotStage S J m ρ).upper xs i ≤ pilotBound μ J ρ (i + 1)),
    zeroSelection ((pilotStage S J m ρ).learnedLaw xs) ρ (4 ^ J) ≤
      16777216 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) := @pilotStage_selection_le
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (S : LearnedStage R) (J m : ℕ) {ρ ε : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (hJ : 1 ≤ J) (hon : PilotOnset μ ρ J) (hm : 0 < m) (hε : 0 < ε) (hmε : 8 * log (2 * (J : ℝ) / ε) ≤ m),
    1 - ε ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | (∀ x : ℝ, (μ.map Subtype.val) (Set.Iic x) ≤
      (pilotStage S J m ρ).learnedLaw (pilotStageWord J m ρ ω) (Set.Iic x)) ∧
      zeroSelection ((pilotStage S J m ρ).learnedLaw (pilotStageWord J m ρ ω)) ρ (4 ^ J) ≤
      16777216 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)} := @original_pilotStage_oracle
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4),
    ∃ J₀ : ℕ, ∀ (q : SignLaw) (S : LearnedStage R) (J m : ℕ) {ε : ℝ}, J₀ ≤ J → 0 < m →
      0 < ε → 8 * log (2 * (J : ℝ) / ε) ≤ m →
      1 - ε ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | (∀ x : ℝ, (μ.map Subtype.val) (Set.Iic x) ≤
      (pilotStage S J m ρ).learnedLaw (pilotStageWord J m ρ ω) (Set.Iic x)) ∧
      zeroSelection ((pilotStage S J m ρ).learnedLaw (pilotStageWord J m ρ ω)) ρ
      (4 ^ J) ≤
      16777216 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)} := @original_pilotStage_oracle_eventually
#print axioms ThresholdHC.ArbitraryLawAdaptation.clippedLaw
#print axioms ThresholdHC.ArbitraryLawAdaptation.clippedLaw_Iic
#print axioms ThresholdHC.ArbitraryLawAdaptation.clippedLaw_Iio_zero
#print axioms ThresholdHC.ArbitraryLawAdaptation.clippedLaw_cdf
#print axioms ThresholdHC.ArbitraryLawAdaptation.clippedLaw_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.clippedLaw_probability
#print axioms ThresholdHC.ArbitraryLawAdaptation.envelopeCDF_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.envelopeCDF_le_above
#print axioms ThresholdHC.ArbitraryLawAdaptation.envelopeCDF_top
#print axioms ThresholdHC.ArbitraryLawAdaptation.envelopeLaw_Iio_zero
#print axioms ThresholdHC.ArbitraryLawAdaptation.le_learnedSlack
#print axioms ThresholdHC.ArbitraryLawAdaptation.learnedSlack
#print axioms ThresholdHC.ArbitraryLawAdaptation.learnedSlack_le_explicit
#print axioms ThresholdHC.ArbitraryLawAdaptation.learnedSlack_le_oracle
#print axioms ThresholdHC.ArbitraryLawAdaptation.learnedSlack_lt_oracle
#print axioms ThresholdHC.ArbitraryLawAdaptation.learned_cdf_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.learned_selection_eventually
#print axioms ThresholdHC.ArbitraryLawAdaptation.learned_selection_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightLaw
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightLaw_apply_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.lightLaw_probability
#print axioms ThresholdHC.ArbitraryLawAdaptation.original_pilotStage_oracle
#print axioms ThresholdHC.ArbitraryLawAdaptation.original_pilotStage_oracle_eventually
#print axioms ThresholdHC.ArbitraryLawAdaptation.pilotBound_le_light
#print axioms ThresholdHC.ArbitraryLawAdaptation.pilotOnset_selection_pos
#print axioms ThresholdHC.ArbitraryLawAdaptation.pilotStage_selection_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.pilotWorkBound
#print axioms ThresholdHC.ArbitraryLawAdaptation.pilotWorkBound_le_oracle
#print axioms ThresholdHC.ArbitraryLawAdaptation.pilotWorkBound_nonneg
#print axioms ThresholdHC.ArbitraryLawAdaptation.quantileTail_cdf
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailUnresolvedMass_le_light
