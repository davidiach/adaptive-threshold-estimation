import ThresholdHC.CriticalEntropy.UniformCoin
import ThresholdHC.EntropyTailUpper.BankErrors

/-! The order on tapes of flips, and stochastic monotonicity in the coin.

Tapes are ordered pointwise, with tails below heads. Flips built from common
uniforms are monotone in the success probability, so an upper set of tapes is
at least as likely under a coin with a larger success probability, and a
lower set at most as likely. The probability of a word of flips is monotone
in the word for a coin with success probability at least `1/2`, and antitone
for one with success probability at most `1/2`. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ThresholdHC.RobustContinuation
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.CriticalEntropy

/-- A flip built from a uniform is monotone in the success probability. -/
theorem uniformCoinFlip_mono {p p' : unitInterval} (h : (p:ℝ) ≤ p') (u : ℝ) :
    uniformCoinFlip p u ≤ uniformCoinFlip p' u := by
  unfold uniformCoinFlip
  by_cases hu : u < (p:ℝ)
  · simp only [hu, lt_of_lt_of_le hu h, ite_true, le_refl]
  · simp only [hu, ite_false]
    exact Bool.false_le _

/-- Tapes built from common uniforms are ordered as their coins are. -/
theorem uniformCoinTape_mono {p p' : unitInterval} (h : (p:ℝ) ≤ p') (u : ℕ → ℝ) :
    uniformCoinTape p u ≤ uniformCoinTape p' u :=
  fun i => uniformCoinFlip_mono h (u i)

/-- An upper set of tapes is at least as likely under the coin with the
larger success probability. -/
theorem tapeMeasure_le_of_isUpperSet {p p' : unitInterval} (h : (p:ℝ) ≤ p')
    {E : Set (ℕ → Bool)} (hE : MeasurableSet E) (hup : IsUpperSet E) :
    tapeMeasure p E ≤ tapeMeasure p' E := by
  have hm : ∀ r : unitInterval, Measurable (uniformCoinTape r) := fun r =>
    measurable_uniformCoinTape.comp (measurable_const.prodMk measurable_id)
  rw [← uniformCoinTape_map p, ← uniformCoinTape_map p', Measure.map_apply (hm p) hE,
    Measure.map_apply (hm p') hE]
  exact measure_mono fun u hu => hup (uniformCoinTape_mono h u) hu

/-- A lower set of tapes is at most as likely under the coin with the larger
success probability. -/
theorem tapeMeasure_le_of_isLowerSet {p p' : unitInterval} (h : (p:ℝ) ≤ p')
    {E : Set (ℕ → Bool)} (hE : MeasurableSet E) (hlow : IsLowerSet E) :
    tapeMeasure p' E ≤ tapeMeasure p E := by
  have hm : ∀ r : unitInterval, Measurable (uniformCoinTape r) := fun r =>
    measurable_uniformCoinTape.comp (measurable_const.prodMk measurable_id)
  rw [← uniformCoinTape_map p, ← uniformCoinTape_map p', Measure.map_apply (hm p) hE,
    Measure.map_apply (hm p') hE]
  exact measure_mono fun u hu => hlow (uniformCoinTape_mono h u) hu

/-- Prefixes of ordered tapes are ordered. -/
theorem tapePrefix_mono (n : ℕ) {ω ω' : ℕ → Bool} (h : ω ≤ ω') :
    tapePrefix n ω ≤ tapePrefix n ω' := fun i => h i.val

/-- The value of a flip is monotone. -/
theorem bit_mono {b b' : Bool} (h : b ≤ b') : bit b ≤ bit b' := by
  cases b with
  | false => cases b' <;> simp [bit]
  | true =>
    cases b' with
    | false => exact absurd h (by decide)
    | true => exact le_rfl

/-- For a coin with success probability at least `1/2`, the probability of a
word of flips does not decrease when tails are turned into heads. -/
theorem streamProb_mono {p : ℝ} (hp : 1/2 ≤ p) (hp1 : p ≤ 1) {n : ℕ} {w w' : Fin n → Bool}
    (h : w ≤ w') : streamProb p w ≤ streamProb p w' := by
  unfold streamProb
  refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
  · split_ifs <;> linarith
  · have hi : w i ≤ w' i := h i
    by_cases hw : w i = true
    · have hw' : w' i = true := Bool.le_iff_imp.mp hi hw
      simp [hw, hw']
    · by_cases hw' : w' i = true
      · have hwf : w i = false := by simpa using hw
        rw [hwf, hw']
        simp only [Bool.false_eq_true, ite_false, ite_true]
        linarith
      · simp [hw, hw']

/-- For a coin with success probability at most `1/2`, the probability of a
word of flips does not increase when tails are turned into heads. -/
theorem streamProb_anti {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2) {n : ℕ} {w w' : Fin n → Bool}
    (h : w ≤ w') : streamProb p w' ≤ streamProb p w := by
  unfold streamProb
  refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
  · split_ifs <;> linarith
  · have hi : w i ≤ w' i := h i
    by_cases hw : w i = true
    · have hw' : w' i = true := Bool.le_iff_imp.mp hi hw
      simp [hw, hw']
    · by_cases hw' : w' i = true
      · have hwf : w i = false := by simpa using hw
        rw [hwf, hw']
        simp only [Bool.false_eq_true, ite_false, ite_true]
        linarith
      · simp [hw, hw']

end ThresholdHC.RobustContinuation
