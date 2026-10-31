import ThresholdHC.EntropyTailAssembly.LevelCertificates

/-! The scheduled bank races consume a positive number of physical flips.
The two bank tests cannot cross at the empty prefix. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal NNReal

namespace ThresholdHC.EntropyTailSampling
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.EntropyTailUpper ThresholdHC.EntropyTailAssembly

theorem probability_weight_le_one (weights : ℕ → ℝ≥0) (hw : HasSum weights 1) (j : ℕ) :
    (weights j:ℝ) ≤ 1 := by
  have h := ENNReal.le_tsum j (f := fun k => (weights k:ℝ≥0∞))
  rw [ENNReal.tsum_coe_eq hw] at h
  exact_mod_cast h

theorem negativeBankTest_zero (weights : ℕ → ℝ≥0) (hw : HasSum weights 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) (w : Fin 0 → Bool) :
    ¬negativeBankTest weights ε 0 w := by
  rintro ⟨j, hj⟩
  have hwj := mul_le_mul_of_nonneg_left (probability_weight_le_one weights hw j) hε
  simp only [streamProb, Fin.prod_univ_zero, mul_one] at hj
  linarith

theorem empty_prefix_preimage (w : Fin 0 → Bool) : tapePrefix 0 ⁻¹' {w} = univ := by
  apply Set.eq_univ_of_forall
  intro ω
  exact Subsingleton.elim _ _

theorem positiveBankTest_zero (μ : Measure Gap) [IsProbabilityMeasure μ]
    (weights : ℕ → ℝ≥0) (hw : HasSum weights 1) {u : ℝ} (hu : u < 1) (w : Fin 0 → Bool) :
    ¬positiveBankTest μ weights u 0 w := by
  let := positiveBankLaw_probability weights hw
  have : IsProbabilityMeasure (allNegativeLaw μ) := by unfold allNegativeLaw; infer_instance
  intro h
  change allNegativeLaw μ (tapePrefix 0 ⁻¹' {w}) ≤
    ENNReal.ofReal u*positiveBankLaw weights (tapePrefix 0 ⁻¹' {w}) at h
  rw [empty_prefix_preimage, measure_univ, measure_univ, mul_one] at h
  have hl : ENNReal.ofReal u < 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr hu
  exact (not_le_of_gt hl) h

theorem raceCost_pos_of_no_empty_crossing (neg pos : PrefixTest)
    (hn : ∀ w : Fin 0 → Bool, ¬neg 0 w) (hp : ∀ w : Fin 0 → Bool, ¬pos 0 w)
    (L : ℕ) (ω : ℕ → Bool) : 0 < raceCost neg pos L ω := by
  have hr : 0 < raceRounds neg pos L ω := by
    by_contra h
    have he : raceRounds neg pos L ω = 0 := by omega
    have hh := raceRounds_hit neg pos L ω
    rw [he] at hh
    rcases hh with h | h | h
    · exact hn _ h
    · exact hp _ h
    · exact (not_le_of_gt (BlindUpper.classifierStop_pos L (parityTape 1 ω))) h
  exact Nat.mul_pos (by norm_num) hr

theorem scheduled_raceCost_pos (μ : Measure Gap) [IsProbabilityMeasure μ]
    (weights : ℕ → ℝ≥0) (hw : HasSum weights 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
    (l L : ℕ) (ω : ℕ → Bool) :
    0 < raceCost (negativeBankTest weights (levelEpsilon l))
      (positiveBankTest μ weights (ρ*levelEpsilon l)) L ω := by
  have he : levelEpsilon l < 1 := by
    unfold levelEpsilon
    have h : (1/16:ℝ)^l ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hu : ρ*levelEpsilon l < 1 := by
    have h := mul_le_mul_of_nonneg_left (levelEpsilon_le_one l) hρ.le
    linarith
  exact raceCost_pos_of_no_empty_crossing _ _
    (negativeBankTest_zero weights hw (levelEpsilon_pos l).le he)
    (positiveBankTest_zero μ weights hw hu) L ω

end ThresholdHC.EntropyTailSampling
