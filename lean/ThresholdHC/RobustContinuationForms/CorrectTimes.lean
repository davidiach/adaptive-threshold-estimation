import ThresholdHC.RobustContinuationForms.Specification

/-! Correct-sign crossing times of the raced classifier.

The race stops no later than any crossing of either bank and no later than
the stop of the ordinary classifier, which in turn stops no later than its
first correct crossing or its terminal check. So the race work is at most
twice either correct-sign time. A downward negative bank and an upward
positive bank keep their correct crossings when the flips move in the
direction of the sign, and the running means of the ordinary classifier move
with the flips, so both correct-sign times decrease. With common uniform
tapes, coins ordered by the sign give tapes ordered by the sign. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ThresholdHC.RobustContinuationForms
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailUpper ThresholdHC.EntropyTailAssembly
open ThresholdHC.RobustContinuation

/-- The race stops by every correct-sign bank crossing. -/
theorem raceRounds_le_bankCorrectTime (neg pos : PrefixTest) (L : ℕ) (s : Bool)
    (ω : ℕ → Bool) : (raceRounds neg pos L ω : ℕ∞) ≤ bankCorrectTime neg pos s ω := by
  unfold bankCorrectTime
  refine le_iInf₂ fun n hn => ?_
  have hh : neg n (Tier2.tapePrefix n (parityTape 0 ω)) ∨
      pos n (Tier2.tapePrefix n (parityTape 0 ω)) := by
    cases s with
    | true => exact Or.inr hn
    | false => exact Or.inl hn
  exact_mod_cast raceRounds_le_bank neg pos L n ω hh

/-- The first correct ordinary crossing, capped at the terminal check. -/
theorem ordinaryCorrectLevel_spec (s : Bool) (L : ℕ) (m : ℕ → ℝ) :
    L ≤ ordinaryCorrectLevel s L m ∨ ordinaryCorrectCross s L m (ordinaryCorrectLevel s L m) := by
  classical
  exact Nat.find_spec (show ∃ k, L ≤ k ∨ ordinaryCorrectCross s L m k from ⟨L, Or.inl le_rfl⟩)

/-- The first correct ordinary crossing comes no later than any correct
crossing and than the terminal check. -/
theorem ordinaryCorrectLevel_le_of (s : Bool) (L : ℕ) (m : ℕ → ℝ) (k : ℕ)
    (hk : L ≤ k ∨ ordinaryCorrectCross s L m k) : ordinaryCorrectLevel s L m ≤ k := by
  classical
  exact Nat.find_min' _ hk

/-- The ordinary classifier stops by its first correct crossing. -/
theorem stopLevel_le_ordinaryCorrectLevel (s : Bool) (L : ℕ) (m : ℕ → ℝ) :
    Tier2.Model.stopLevel m L ≤ ordinaryCorrectLevel s L m := by
  rcases ordinaryCorrectLevel_spec s L m with hL | hc
  · exact (Tier2.Model.stopLevel_le m L).trans hL
  · apply Uniform713.firstStop_le_of_cross
    cases s with
    | true =>
      change Tier2.Model.threshold1 (Uniform713.cap (ordinaryCorrectLevel true L m))
        (Uniform713.cap L) < m (ordinaryCorrectLevel true L m) - 1/2 at hc
      exact hc.trans_le (le_abs_self _)
    | false =>
      change Tier2.Model.threshold1 (Uniform713.cap (ordinaryCorrectLevel false L m))
        (Uniform713.cap L) < 1/2 - m (ordinaryCorrectLevel false L m) at hc
      refine hc.trans_le ?_
      rw [abs_sub_comm]
      exact le_abs_self _

/-- The ordinary classifier reads at most `T_ord^s` flips. -/
theorem classifierStop_le_ordinaryCorrectTime (s : Bool) (L : ℕ) (ω : ℕ → Bool) :
    BlindUpper.classifierStop L ω ≤ ordinaryCorrectTime s L ω :=
  Nat.pow_le_pow_right (by norm_num) (stopLevel_le_ordinaryCorrectLevel s L _)

/-- (iii-a) The race work is at most twice the earlier correct-sign time. -/
theorem correct_time_race_bound_proof : CorrectTimeRaceBoundStatement := by
  intro neg pos L s ω
  have h1 := raceRounds_le_bankCorrectTime neg pos L s ω
  have h2 : (raceRounds neg pos L ω : ℕ∞) ≤ (ordinaryCorrectTime s L (parityTape 1 ω) : ℕ∞) := by
    exact_mod_cast (raceRounds_le_ordinary neg pos L ω).trans
      (classifierStop_le_ordinaryCorrectTime s L _)
  unfold raceCost
  push_cast
  exact mul_le_mul_right (le_min h1 h2) 2

/-- The correct-sign bank time decreases in the sign-directed order. -/
theorem bankCorrectTime_anti {neg pos : PrefixTest} (hneg : DownwardTest neg)
    (hpos : UpwardTest pos) (s : Bool) {ω₀ ω₁ : ℕ → Bool} (h : SignOrdered s ω₀ ω₁) :
    bankCorrectTime neg pos s ω₁ ≤ bankCorrectTime neg pos s ω₀ := by
  unfold bankCorrectTime
  refine le_iInf₂ fun n hn => iInf₂_le n ?_
  cases s with
  | true =>
    change ω₀ ≤ ω₁ at h
    exact hpos n _ _ (tapePrefix_mono n (parityTape_mono 0 h)) hn
  | false =>
    change ω₁ ≤ ω₀ at h
    exact hneg n _ _ (tapePrefix_mono n (parityTape_mono 0 h)) hn

/-- The correct-sign ordinary time decreases in the sign-directed order. -/
theorem ordinaryCorrectTime_anti (s : Bool) (L : ℕ) {ω₀ ω₁ : ℕ → Bool}
    (h : SignOrdered s ω₀ ω₁) :
    ordinaryCorrectTime s L (parityTape 1 ω₁) ≤ ordinaryCorrectTime s L (parityTape 1 ω₀) := by
  unfold ordinaryCorrectTime
  apply Nat.pow_le_pow_right (by norm_num)
  apply ordinaryCorrectLevel_le_of
  rcases ordinaryCorrectLevel_spec s L
    (fun k => Uniform713.dyadicMean Tier2.observations k (parityTape 1 ω₀)) with hL | hc
  · exact Or.inl hL
  · right
    cases s with
    | true =>
      change ω₀ ≤ ω₁ at h
      have hm := dyadicMean_mono (ordinaryCorrectLevel true L
        (fun k => Uniform713.dyadicMean Tier2.observations k (parityTape 1 ω₀)))
        (parityTape_mono 1 h)
      change _ < _ - 1/2 at hc
      change _ < _ - 1/2
      linarith
    | false =>
      change ω₁ ≤ ω₀ at h
      have hm := dyadicMean_mono (ordinaryCorrectLevel false L
        (fun k => Uniform713.dyadicMean Tier2.observations k (parityTape 1 ω₀)))
        (parityTape_mono 1 h)
      change _ < 1/2 - _ at hc
      change _ < 1/2 - _
      linarith

/-- (iii-b) Both correct-sign times decrease in the sign-directed order. -/
theorem correct_time_antitone_proof : CorrectTimeAntitoneStatement :=
  fun _ _ hneg hpos L s _ _ h => ⟨bankCorrectTime_anti hneg hpos s h, ordinaryCorrectTime_anti s L h⟩

/-- Coins ordered by the sign give common-uniform tapes ordered by the sign. -/
theorem signOrdered_uniformCoinTape (s : Bool) {p₀ p : unitInterval}
    (h : cond s ((p₀:ℝ) ≤ p) ((p:ℝ) ≤ p₀)) (u : ℕ → ℝ) :
    SignOrdered s (CriticalEntropy.uniformCoinTape p₀ u) (CriticalEntropy.uniformCoinTape p u) := by
  cases s with
  | true => exact uniformCoinTape_mono h u
  | false => exact uniformCoinTape_mono h u

/-- `(UA15)` on ordered tapes. -/
theorem ordered_correct_time_work {neg pos : PrefixTest} (hneg : DownwardTest neg)
    (hpos : UpwardTest pos) (L : ℕ) (s : Bool) {ω₀ ω₁ : ℕ → Bool} (h : SignOrdered s ω₀ ω₁) :
    (raceCost neg pos L ω₁ : ℕ∞) ≤
      2 * min (bankCorrectTime neg pos s ω₁) (ordinaryCorrectTime s L (parityTape 1 ω₁) : ℕ∞) ∧
    2 * min (bankCorrectTime neg pos s ω₁) (ordinaryCorrectTime s L (parityTape 1 ω₁) : ℕ∞) ≤
      2 * min (bankCorrectTime neg pos s ω₀) (ordinaryCorrectTime s L (parityTape 1 ω₀) : ℕ∞) := by
  refine ⟨correct_time_race_bound_proof neg pos L s ω₁, mul_le_mul_right ?_ 2⟩
  exact min_le_min (bankCorrectTime_anti hneg hpos s h)
    (by exact_mod_cast ordinaryCorrectTime_anti s L h)

/-- (iii-c) `(UA15)` under the common-uniform coupling. -/
theorem coupled_correct_time_work_proof : CoupledCorrectTimeWorkStatement :=
  fun _ _ hneg hpos L s _ _ h u =>
    ordered_correct_time_work hneg hpos L s (signOrdered_uniformCoinTape s h u)

/-- The coins of two gaps of one sign are ordered by the sign. -/
theorem gapParameter_signOrder (s : Bool) {d₀ d : Gap} (h : (d₀:ℝ) ≤ d) :
    cond s (((ObservableSimulation.gapParameter s d₀ : unitInterval) : ℝ) ≤
        (ObservableSimulation.gapParameter s d : unitInterval))
      (((ObservableSimulation.gapParameter s d : unitInterval) : ℝ) ≤
        (ObservableSimulation.gapParameter s d₀ : unitInterval)) := by
  cases s with
  | true => change 1/2 + (d₀:ℝ) ≤ 1/2 + (d:ℝ); linarith
  | false => change 1/2 + -(d:ℝ) ≤ 1/2 + -(d₀:ℝ); linarith

/-- (iii-c, gaps) `(UA15)` for a reference gap below the true gap. -/
theorem coupled_gap_correct_time_work_proof : CoupledGapCorrectTimeWorkStatement :=
  fun neg pos hneg hpos L s _ _ h u =>
    coupled_correct_time_work_proof neg pos hneg hpos L s _ _ (gapParameter_signOrder s h) u

/-- The fair coin and a coin of gap `d` are ordered by the sign of the latter. -/
theorem fair_signOrder (s : Bool) (d : Gap) {p₀ : unitInterval} (h : (p₀:ℝ) = 1/2) :
    cond s ((p₀:ℝ) ≤ (ObservableSimulation.gapParameter s d : unitInterval))
      (((ObservableSimulation.gapParameter s d : unitInterval) : ℝ) ≤ p₀) := by
  have hd := d.property.1
  cases s with
  | true => change (p₀:ℝ) ≤ 1/2 + (d:ℝ); linarith
  | false => change 1/2 + -(d:ℝ) ≤ (p₀:ℝ); linarith

/-- (iii-c, zero atom) `(UA15)` for the reference zero atom. -/
theorem coupled_zero_atom_correct_time_work_proof : CoupledZeroAtomCorrectTimeWorkStatement :=
  fun neg pos hneg hpos L s d _ h u =>
    coupled_correct_time_work_proof neg pos hneg hpos L s _ _ (fair_signOrder s d h) u

/-- (iii-d) `(UA15)` for the level race of the reference design. -/
theorem reference_race_correct_time_work_proof : ReferenceRaceCorrectTimeWorkStatement := by
  intro η _ w hw c hc ρ hρc κ l s p₀ p h u
  exact coupled_correct_time_work_proof (negativeBankTest w (levelEpsilon l))
    (positiveBankTest η w (ρ*levelEpsilon l/c)) (negativeBankTest_downward w (levelEpsilon_pos l).le)
    (positiveBankTest_upward η w _) (2 * κ l) s p₀ p h u

end ThresholdHC.RobustContinuationForms
