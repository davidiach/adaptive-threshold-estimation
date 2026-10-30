import ThresholdHC.EntropyTailUpper.NullMixture
import ThresholdHC.EntropyTailUpper.SurvivalWork
import ThresholdHC.EntropyTailUpper.PrefixConcentration

/-! Positive-sign raced work from an explicit null Laplace envelope. The
envelope is a property of the full population law, not a hidden-label oracle. -/

noncomputable section
open MeasureTheory Set Real
open scoped NNReal BigOperators

namespace ThresholdHC.EntropyTailUpper
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.Uniform713

theorem measurable_raceRounds (neg pos : PrefixTest) (L : ℕ) :
    Measurable (raceRounds neg pos L) := by
  have h : raceRounds neg pos L = (fun n : ℕ => n/2) ∘ raceCost neg pos L := by
    funext ω
    simp [raceCost]
  rw [h]
  exact (measurable_of_countable _).comp (measurable_raceCost neg pos L)

theorem prefix_count_eq (n : ℕ) (hn : 0 < n) (ω : ℕ → Bool) :
    (∑ i : Fin n, bit (tapePrefix n ω i)) = n*prefixMean observations n ω := by
  simp only [tapePrefix, prefixMean, observations]
  rw [Fin.sum_univ_eq_sum_range (fun i => bit (ω i))]
  have : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem positive_race_survival (μ : Measure Gap) [IsProbabilityMeasure μ]
    (weights : ℕ → ℝ≥0) (ε : ℝ) {u V U : ℝ} (hu : 0 ≤ u)
    (j L : ℕ) (d : Gap) (hd : d ∈ EntropyTail.band j)
    {n : ℕ} (hn : 0 < n) (hU : U ≤ n*(d:ℝ)^2/3)
    (hLap : nullLaplace μ n ≤ V) (hV : V ≤ u*(weights j:ℝ)*exp U) :
    (tapeMeasure (gapParameter true d)).real
      {ω | n < raceRounds (negativeBankTest weights ε) (positiveBankTest μ weights u) L ω} ≤
        exp (-(n:ℝ)*(d:ℝ)^2/2) := by
  let bad := {ω | (d:ℝ)/2 ≤ (gapParameter true d:ℝ)-prefixMean observations n ω}
  have hs : {ω | n < raceRounds (negativeBankTest weights ε) (positiveBankTest μ weights u) L ω} ⊆
      parityTape 0 ⁻¹' bad := by
    intro ω hnω
    by_contra hb
    have hm : (d:ℝ)/2 ≤ prefixMean observations n (parityTape 0 ω)-1/2 := by
      change ¬ ((d:ℝ)/2 ≤ (gapParameter true d:ℝ)-prefixMean observations n (parityTape 0 ω)) at hb
      change ¬ ((d:ℝ)/2 ≤ 1/2+(d:ℝ)-prefixMean observations n (parityTape 0 ω)) at hb
      linarith
    have hc : (n:ℝ)/2 ≤ ∑ i : Fin n, bit (tapePrefix n (parityTape 0 ω) i) := by
      rw [prefix_count_eq n hn]
      nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) d.property.1.le]
    have hscore := positive_prefix_score_lower d.property.1.le
      (r := EntropyTail.bandEdge j/4) (by positivity [EntropyTail.bandEdge_pos j])
      (by linarith [bandEdge_le_half j]) (by linarith [hd.2]) (by linarith [hd.1]) hn (parityTape 0 ω) hm
    have hnull := (null_prefix_gaussian_ennreal μ (tapePrefix n (parityTape 0 ω)) hc).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hLap
        (CriticalEntropy.streamProb_pos (1/2) (by norm_num) (by norm_num) _).le))
    have hhit := positive_bank_of_score μ weights hu j (tapePrefix n (parityTape 0 ω)) hnull
      (hV.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (hU.trans hscore))
        (mul_nonneg hu (weights j).property)))
    exact (not_le_of_gt hnω) (raceRounds_le_bank _ _ L n ω (Or.inr hhit))
  have h := measureReal_mono (μ := tapeMeasure (gapParameter true d)) hs
  rw [parityTape_event 0 _ (E := bad) (measurableSet_le measurable_const
    (measurable_const.sub (measurable_prefixMean measurable_observations n)))] at h
  have ht := tape_prefix_lower_tail (gapParameter true d) hn (t := (d:ℝ)/2) (by positivity [d.property.1])
  apply h.trans
  convert ht using 1
  congr 1
  ring

theorem positive_raceRounds_work (μ : Measure Gap) [IsProbabilityMeasure μ]
    (weights : ℕ → ℝ≥0) (ε : ℝ) {u V U : ℝ} (hu : 0 ≤ u) (hU : 1 ≤ U)
    (j L : ℕ) (d : Gap) (hd : d ∈ EntropyTail.band j)
    (hLap : ∀ n : ℕ, 1 ≤ n*(d:ℝ)^2 → nullLaplace μ n ≤ V)
    (hV : V ≤ u*(weights j:ℝ)*exp U) :
    (∫ ω, (raceRounds (negativeBankTest weights ε) (positiveBankTest μ weights u) L ω : ℝ)
      ∂tapeMeasure (gapParameter true d)) ≤ 6*U/(d:ℝ)^2 := by
  let N : ℕ := ⌈3*U/(d:ℝ)^2⌉₊
  have hd2 : 0 < (d:ℝ)^2 := sq_pos_of_pos d.property.1
  have hNpos : 0 < N := Nat.ceil_pos.mpr (div_pos (by linarith) hd2)
  have htail (n : ℕ) (hn : N ≤ n) :
      (tapeMeasure (gapParameter true d)).real
        {ω | n < raceRounds (negativeBankTest weights ε) (positiveBankTest μ weights u) L ω} ≤
          exp (-(d:ℝ)^2/2)^n := by
    have hnr : 3*U ≤ n*(d:ℝ)^2 := (div_le_iff₀ hd2).mp (Nat.ceil_le.mp hn)
    have h := positive_race_survival μ weights ε hu j L d hd (hNpos.trans_le hn)
      (by linarith : U ≤ n*(d:ℝ)^2/3) (hLap n (by linarith)) hV
    rw [← exp_nat_mul]
    convert h using 1
    congr 1
    ring
  have hwork := geometric_work_bound (gapParameter true d)
    (raceRounds (negativeBankTest weights ε) (positiveBankTest μ weights u) L) (2^L) N
    (raceRounds_le _ _ L) (measurable_raceRounds _ _ L) (exp_pos _).le
    (exp_lt_one_iff.mpr (by linarith : -(d:ℝ)^2/2 < 0)) htail
  have hi := inv_one_sub_exp_neg_le (show 0 < (d:ℝ)^2/2 by positivity)
  have hN : (N:ℝ) ≤ 3*U/(d:ℝ)^2+1 := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 3*U/(d:ℝ)^2)).le
  have he : ((d:ℝ)^2/2)⁻¹ = 2/(d:ℝ)^2 := by field_simp
  rw [show -((d:ℝ)^2/2) = -(d:ℝ)^2/2 by ring, he] at hi
  apply hwork.trans
  have hh := add_le_add hN hi
  apply hh.trans
  apply (le_div_iff₀ hd2).mpr
  have hd2max : (d:ℝ)^2 ≤ 1/4 := by nlinarith [d.property.1, d.property.2]
  have hcancel : (3*U/(d:ℝ)^2+1+(1+2/(d:ℝ)^2))*(d:ℝ)^2 = 3*U+2*(d:ℝ)^2+2 := by
    field_simp [d.property.1.ne']
    ring
  rw [hcancel]
  nlinarith

end ThresholdHC.EntropyTailUpper
