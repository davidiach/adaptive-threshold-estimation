import ThresholdHC.EntropyTailUpper.PrefixCrossing
import ThresholdHC.EntropyTailUpper.BernoulliTilt
import ThresholdHC.EntropyTailQuantile.MeasureEntropy
import ThresholdHC.ObservableSimulation.OriginalExperiment

/-! Error bounds for the weighted reference bank, using the full null mixture.
No termination assumption is imposed on the uncapped bank. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal NNReal BigOperators

namespace ThresholdHC.EntropyTailUpper
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation

theorem tape_prefix_mass (p : unitInterval) (n : ℕ) (w : Fin n → Bool) :
    tapeMeasure p (tapePrefix n ⁻¹' {w}) = ENNReal.ofReal (streamProb p w) := by
  calc
    _ = ((tapeMeasure p).map (tapePrefix n)) {w} :=
      (Measure.map_apply (measurable_prefix n) (measurableSet_singleton w)).symm
    _ = (finiteMeasure p n) {w} := by rw [prefix_map]
    _ = _ := by rw [← ofReal_measureReal, finiteMeasure_real_singleton]

theorem negative_reference_error (p : unitInterval) {r c : ℝ}
    (hp : 1/2 ≤ (p:ℝ)) (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) (hc : 0 ≤ c) :
    tapeMeasure p (everPrefixHit (fun _ w => streamProb (1/2) w ≤ c * streamProb (1/2-r) w)) ≤
      ENNReal.ofReal c := by
  apply measure_everPrefixHit_le _ (tapeMeasure p)
    (tapeMeasure (tiltedParameter p hp hr0 hr1))
  intro n w hcross
  rw [tape_prefix_mass, tape_prefix_mass, ← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal (negative_reference_crossing_dominates p hp hr0 hr1 hc w hcross)

theorem bandEdge_le_half (j : ℕ) : EntropyTail.bandEdge j ≤ 1/2 := by
  simpa [EntropyTail.bandEdge] using EntropyTail.bandEdge_antitone (Nat.zero_le j)

def negativeBankEvent (weights : ℕ → ℝ≥0) (ε : ℝ) : Set (ℕ → Bool) :=
  ⋃ j : ℕ, everPrefixHit (fun _ w => streamProb (1/2) w ≤
    (ε*(weights j:ℝ)) * streamProb (1/2-EntropyTail.bandEdge j/2) w)

theorem negative_bank_error (weights : ℕ → ℝ≥0) (hweights : HasSum weights 1) {ε : ℝ} (hε : 0 ≤ ε)
    (p : unitInterval) (hp : 1/2 ≤ (p:ℝ)) :
    tapeMeasure p (negativeBankEvent weights ε) ≤ ENNReal.ofReal ε := by
  apply (measure_iUnion_le _).trans
  calc
    _ ≤ ∑' j, ENNReal.ofReal (ε*(weights j:ℝ)) := by
      apply ENNReal.tsum_le_tsum
      intro j
      exact negative_reference_error p hp
        (div_nonneg (EntropyTail.bandEdge_pos j).le (by norm_num))
        (by linarith [bandEdge_le_half j]) (mul_nonneg hε (weights j).property)
    _ = ENNReal.ofReal ε * ∑' j, (weights j:ℝ≥0∞) := by
      simp only [ENNReal.ofReal_mul hε, ENNReal.ofReal_coe_nnreal, ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal ε := by rw [ENNReal.tsum_coe_eq hweights]; simp

def positiveReference (j : ℕ) : unitInterval :=
  ⟨1/2+EntropyTail.bandEdge j/4, by
    have hp := EntropyTail.bandEdge_pos j
    have hb := bandEdge_le_half j
    constructor <;> linarith⟩

def positiveBankLaw (weights : ℕ → ℝ≥0) : Measure (ℕ → Bool) :=
  Measure.sum (fun j => (weights j:ℝ≥0∞) • tapeMeasure (positiveReference j))

theorem positiveBankLaw_probability (weights : ℕ → ℝ≥0) (hweights : HasSum weights 1) :
    IsProbabilityMeasure (positiveBankLaw weights) := by
  constructor
  simp only [positiveBankLaw, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  simpa using ENNReal.tsum_coe_eq hweights

def allNegativeSignLaw : SignLaw := ⟨fun _ => 0, measurable_const, fun _ => by norm_num⟩

def allNegativeLaw (μ : Measure Gap) : Measure (ℕ → Bool) :=
  originalPopulationTapeLaw μ allNegativeSignLaw

def positiveBankEvent (μ : Measure Gap) (weights : ℕ → ℝ≥0) (u : ℝ) : Set (ℕ → Bool) :=
  everPrefixHit (fun n w => allNegativeLaw μ (tapePrefix n ⁻¹' {w}) ≤
    ENNReal.ofReal u * positiveBankLaw weights (tapePrefix n ⁻¹' {w}))

theorem positive_bank_error (μ : Measure Gap) (weights : ℕ → ℝ≥0) (hweights : HasSum weights 1) (u : ℝ) :
    allNegativeLaw μ (positiveBankEvent μ weights u) ≤ ENNReal.ofReal u := by
  have := positiveBankLaw_probability weights hweights
  exact measure_everPrefixHit_le _ (allNegativeLaw μ) (positiveBankLaw weights) (ENNReal.ofReal u)
    (fun _ _ h => h)

end ThresholdHC.EntropyTailUpper
