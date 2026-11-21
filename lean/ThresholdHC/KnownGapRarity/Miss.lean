import ThresholdHC.KnownGapRarity.Estimator
import ThresholdHC.FixedPlan.Tail
import ThresholdHC.EntropyTailUpper.PrefixConcentration

/-! The misclassification probability of the majority of `m = 2k+1` flips at gap
`d` is at most `exp(-2 m d^2)` (Hoeffding). With `m >= log(2B)/(2d^2)` this gives
`f <= 1/(2B)`, and `f <= 1/4` once `B >= 2m`. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThresholdHC.KnownGapRarity
open ThresholdHC.Tier6 ThresholdHC.FixedPlan ThresholdHC.Tier2 ThresholdHC.Uniform713
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation

theorem wordHeads_prefix_cast (n : ℕ) (ω : ℕ → Bool) :
    ((wordHeads (tapePrefix n ω) : ℕ) : ℝ) = ∑ i ∈ Finset.range n, observations i ω := by
  rw [wordHeads_eq_sum]
  push_cast
  rw [← Fin.sum_univ_eq_sum_range (fun i => observations i ω) n]
  apply Finset.sum_congr rfl
  intro i _
  cases h : ω i <;> simp [observations, bit, tapePrefix, h]

/-- Hoeffding bound for the majority vote: `f <= exp(-2 m d^2)` with `m = 2k+1`. -/
theorem majorityMiss_le_exp (k : ℕ) (d : Gap) :
    majorityMiss k d ≤ Real.exp (-2 * ((2*k+1 : ℕ) : ℝ) * (d:ℝ)^2) := by
  rw [← majorityVote_error k d false]
  refine le_trans (measureReal_mono ?_) (EntropyTailUpper.tape_prefix_upper_tail
    (gapParameter false d) (n := 2*k+1) (by omega) (t := d) d.property.1.le)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have hv : k+1 ≤ wordHeads (tapePrefix (2*k+1) ω) := by
    by_contra hc
    apply hω
    simp [majorityVote, hc, bit]
  have hc : ((k+1 : ℕ) : ℝ) ≤ ((wordHeads (tapePrefix (2*k+1) ω) : ℕ) : ℝ) := by exact_mod_cast hv
  rw [wordHeads_prefix_cast] at hc
  rw [gapParameter_false_val]
  unfold prefixMean
  have hpos : (0:ℝ) < ((2*k+1 : ℕ) : ℝ) := by positivity
  rw [le_sub_iff_add_le, le_div_iff₀ hpos]
  push_cast at hc ⊢
  linarith

theorem missRate_nonneg (d : Gap) (B : ℝ) : 0 ≤ missRate d B := majorityMiss_nonneg _ d

/-- `f <= 1/(2B)`. -/
theorem missRate_le (d : Gap) {B : ℝ} (hB : 0 < B) : missRate d B ≤ 1 / (2*B) := by
  have h1 := majorityMiss_le_exp (flipIndex d B) d
  have h2 := flipCount_ge d B
  have hd : 0 < (d:ℝ) := d.property.1
  unfold missRate
  refine h1.trans ?_
  have h3 : Real.log (2*B) ≤ 2 * ((2 * flipIndex d B + 1 : ℕ) : ℝ) * (d:ℝ)^2 := by
    rw [div_le_iff₀ (by positivity)] at h2
    unfold flipCount at h2
    linarith
  calc Real.exp (-2 * ((2*flipIndex d B+1 : ℕ) : ℝ) * (d:ℝ)^2)
      ≤ Real.exp (-Real.log (2*B)) := Real.exp_le_exp.mpr (by linarith)
    _ = 1/(2*B) := by rw [Real.exp_neg, Real.exp_log (by positivity), one_div]

/-- `f <= 1/4` once `B >= 2m`. -/
theorem missRate_le_quarter {d : Gap} {B : ℝ} (h : 2 * (flipCount d B : ℝ) ≤ B) :
    missRate d B ≤ 1/4 := by
  have hm : (1 : ℝ) ≤ flipCount d B := by exact_mod_cast flipCount_pos d B
  have hB : 2 ≤ B := by linarith
  refine (missRate_le d (by linarith)).trans ?_
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

theorem one_sub_two_missRate {d : Gap} {B : ℝ} (h : 2 * (flipCount d B : ℝ) ≤ B) :
    1/2 ≤ 1 - 2 * missRate d B := by
  have := missRate_le_quarter h
  linarith

end ThresholdHC.KnownGapRarity
