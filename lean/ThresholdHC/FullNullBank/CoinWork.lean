import ThresholdHC.FullNullBank.Bank
import ThresholdHC.RobustContinuation.RobustCoinWork

/-! The work of the race with the full-null bank on a coin with a larger gap
than the reference gap `d0`.

* On a negative coin the race stops by the crossing time of the matching
  negative reference, whatever the positive test is; the bound of
  `RobustContinuation.bank_race_negative_work_of_le` holds for every positive
  test.
* On a positive coin the race has stopped once the running mean of the bank's
  flips is above `1/2 + d0/2` and the positive test fires there. For the
  full-null bank this holds when `z0 + (1 - z0) nullLaplace eta n` is within the
  allowance, and `(1 - z0) nullLaplace eta n` is the null Laplace transform of
  the design `sigma + tau + zeta = (1 - z0) eta`. The fair-coin term `z0` does
  not decay, and is carried in the envelope `z0 + threePieceEnvelope`. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal NNReal BigOperators

namespace ThresholdHC.FullNullBank
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.Uniform713 ThresholdHC.BlindUpper ThresholdHC.CriticalEntropy
open ThresholdHC.EntropyTailUpper ThresholdHC.EntropyTailAssembly ThresholdHC.RobustContinuation

/-- The race with the negative bank stops by the crossing time of the matching
negative reference score, for every positive test. -/
theorem raceRounds_le_negativeScore (pos : PrefixTest) (weights : ℕ → ℝ≥0) {ε : ℝ}
    (hε : 0 < ε) (j L : ℕ) (hw : 0 < (weights j:ℝ)) (ω : ℕ → Bool) :
    raceRounds (negativeBankTest weights ε) pos L ω ≤
      scoreStop (negativeBitScore (EntropyTailQuantile.bandEdge j/2)) (log (ε*(weights j:ℝ))⁻¹)
        (2^L) (parityTape 0 ω) := by
  let f := negativeBitScore (EntropyTailQuantile.bandEdge j/2)
  let b := log (ε*(weights j:ℝ))⁻¹
  rcases (boundedFirst_spec (fun n => scoreTest f b n (tapePrefix n (parityTape 0 ω))) (2^L)).2
    with h | h
  · apply raceRounds_le_bank
    apply Or.inl
    refine ⟨j, ?_⟩
    exact negative_score_crossing (by positivity [EntropyTailQuantile.bandEdge_pos j])
      (by linarith [bandEdge_le_half j]) (mul_pos hε hw) _ h
  · change scoreStop f b (2^L) (parityTape 0 ω) = 2^L at h
    change _ ≤ scoreStop f b (2^L) (parityTape 0 ω)
    rw [h]
    exact raceRounds_le _ _ L ω

/-- The work of the race with the negative bank on a negative coin of gap
`d ≥ d₀`, for a reference gap `d₀` in band `j`, for every positive test. -/
theorem race_negative_work_of_le (pos : PrefixTest) (weights : ℕ → ℝ≥0) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (j L : ℕ) (hw : 0 < (weights j:ℝ))
    (hw1 : (weights j:ℝ) ≤ 1) {d₀ d : Gap} (hd : d₀ ∈ EntropyTailQuantile.band j)
    (h : (d₀:ℝ) ≤ d) :
    conditionalRaceWork (negativeBankTest weights ε) pos L false d ≤
      (3/(2*(d₀:ℝ)^2))*(1+log (ε*(weights j:ℝ))⁻¹) := by
  let f := negativeBitScore (EntropyTailQuantile.bandEdge j/2)
  let b := log (ε*(weights j:ℝ))⁻¹
  have hi := (parityTape_measurePreserving 0 (gapParameter false d)).integrable_comp_of_integrable
    (integrable_scoreStop (gapParameter false d) f b (2^L))
  have hle := integral_mono (integrable_raceCost _ _ L _) (hi.const_mul 2)
    (fun ω => show (raceCost (negativeBankTest weights ε) pos L ω : ℝ) ≤
        2*(scoreStop f b (2^L) (parityTape 0 ω) : ℝ) by
      exact_mod_cast Nat.mul_le_mul_left 2 (raceRounds_le_negativeScore pos weights hε j L hw ω))
  rw [integral_const_mul] at hle
  dsimp only [Function.comp_apply] at hle
  rw [parityTape_integral 0 _ (fun ω => (scoreStop f b (2^L) ω : ℝ))
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
      (measurable_prefixSearchCost (scoreTest f b) (2^L)))] at hle
  have hprod : ε*(weights j:ℝ) ≤ 1 :=
    (mul_le_mul_of_nonneg_right hε1 hw.le).trans (by simpa using hw1)
  have hb : 0 ≤ b := log_nonneg (one_le_inv₀ (mul_pos hε hw) |>.mpr hprod)
  have hwk := negative_scoreStop_work_of_le h (r := EntropyTailQuantile.bandEdge j/2)
    (by positivity [EntropyTailQuantile.bandEdge_pos j]) (by linarith [bandEdge_le_half j])
    (by linarith [hd.2]) hd.1.le hb (2^L)
  unfold conditionalRaceWork
  calc
    _ ≤ 2*(∫ ω, (scoreStop f b (2^L) ω : ℝ) ∂tapeMeasure (gapParameter false d)) := hle
    _ ≤ 2*((3/(4*(d₀:ℝ)^2))*(1+b)) := mul_le_mul_of_nonneg_left hwk (by norm_num)
    _ = _ := by dsimp [b]; ring

/-- Survival of a race on a positive coin of gap `d ≥ d₀`, for a reference
gap `d₀` in band `j`, when the positive test fires at round `n` on every word
with at least half heads whose score is above the allowance. -/
theorem positive_race_survival_of_fire (neg pos : PrefixTest) (weights : ℕ → ℝ≥0)
    {u V U : ℝ} (hu : 0 ≤ u) (j L : ℕ) {d₀ d : Gap} (hd : d₀ ∈ EntropyTailQuantile.band j)
    (h : (d₀:ℝ) ≤ d) {n : ℕ} (hn : 0 < n) (hU : U ≤ n*(d₀:ℝ)^2/3)
    (hfire : ∀ w : Fin n → Bool, (n:ℝ)/2 ≤ ∑ i, bit (w i) →
      V ≤ u*(weights j:ℝ)*exp (∑ i, positiveBitScore (EntropyTailQuantile.bandEdge j/4) (w i)) →
      pos n w)
    (hV : V ≤ u*(weights j:ℝ)*exp U) :
    (tapeMeasure (gapParameter true d)).real {ω | n < raceRounds neg pos L ω} ≤
        exp (-(n:ℝ)*(d₀:ℝ)^2/2) := by
  let bad := {ω | (d₀:ℝ)/2 ≤ (gapParameter true d₀:ℝ)-prefixMean observations n ω}
  have hbadm : MeasurableSet bad := measurableSet_le measurable_const
    (measurable_const.sub (measurable_prefixMean measurable_observations n))
  have hs : {ω | n < raceRounds neg pos L ω} ⊆ parityTape 0 ⁻¹' bad := by
    intro ω hnω
    by_contra hb
    have hm : (d₀:ℝ)/2 ≤ prefixMean observations n (parityTape 0 ω)-1/2 := by
      change ¬ ((d₀:ℝ)/2 ≤
        (gapParameter true d₀:ℝ)-prefixMean observations n (parityTape 0 ω)) at hb
      change ¬ ((d₀:ℝ)/2 ≤ 1/2+(d₀:ℝ)-prefixMean observations n (parityTape 0 ω)) at hb
      linarith
    have hc : (n:ℝ)/2 ≤ ∑ i : Fin n, bit (tapePrefix n (parityTape 0 ω) i) := by
      rw [prefix_count_eq n hn]
      nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) d₀.property.1.le]
    have hscore := positive_prefix_score_lower d₀.property.1.le
      (r := EntropyTailQuantile.bandEdge j/4) (by positivity [EntropyTailQuantile.bandEdge_pos j])
      (by linarith [bandEdge_le_half j]) (by linarith [hd.2]) (by linarith [hd.1]) hn
      (parityTape 0 ω) hm
    have hhit := hfire (tapePrefix n (parityTape 0 ω)) hc
      (hV.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (hU.trans hscore))
        (mul_nonneg hu (weights j).property)))
    exact (not_le_of_gt hnω) (raceRounds_le_bank _ _ L n ω (Or.inr hhit))
  have h1 := measureReal_mono (μ := tapeMeasure (gapParameter true d)) hs
  rw [parityTape_event 0 _ (E := bad) hbadm] at h1
  have hlow : IsLowerSet bad := by
    intro a b hba ha
    have hmono := prefixMean_mono n hba
    change (d₀:ℝ)/2 ≤ (gapParameter true d₀:ℝ)-prefixMean observations n b
    have ha' : (d₀:ℝ)/2 ≤ (gapParameter true d₀:ℝ)-prefixMean observations n a := ha
    linarith
  have h2 : (tapeMeasure (gapParameter true d)).real bad ≤
      (tapeMeasure (gapParameter true d₀)).real bad :=
    ENNReal.toReal_mono (measure_ne_top _ _)
      (tapeMeasure_le_of_isLowerSet (p := gapParameter true d₀) (p' := gapParameter true d)
        (by change 1/2 + (d₀:ℝ) ≤ 1/2 + (d:ℝ); linarith) hbadm hlow)
  have ht := tape_prefix_lower_tail (gapParameter true d₀) hn (t := (d₀:ℝ)/2)
    (by positivity [d₀.property.1])
  apply (h1.trans h2).trans
  convert ht using 1
  congr 1
  ring

/-- The number of rounds of a race on a positive coin of gap `d ≥ d₀`, for a
reference gap `d₀` in band `j`, when the positive test fires above the
allowance at every round `n` with `n d₀² ≥ 1`. -/
theorem positive_raceRounds_work_of_fire (neg pos : PrefixTest) (weights : ℕ → ℝ≥0)
    {u V U : ℝ} (hu : 0 ≤ u) (hU : 1 ≤ U) (j L : ℕ) {d₀ d : Gap}
    (hd : d₀ ∈ EntropyTailQuantile.band j) (h : (d₀:ℝ) ≤ d)
    (hfire : ∀ n : ℕ, 1 ≤ n*(d₀:ℝ)^2 → ∀ w : Fin n → Bool, (n:ℝ)/2 ≤ ∑ i, bit (w i) →
      V ≤ u*(weights j:ℝ)*exp (∑ i, positiveBitScore (EntropyTailQuantile.bandEdge j/4) (w i)) →
      pos n w)
    (hV : V ≤ u*(weights j:ℝ)*exp U) :
    (∫ ω, (raceRounds neg pos L ω : ℝ) ∂tapeMeasure (gapParameter true d)) ≤
      6*U/(d₀:ℝ)^2 := by
  let N : ℕ := ⌈3*U/(d₀:ℝ)^2⌉₊
  have hd2 : 0 < (d₀:ℝ)^2 := sq_pos_of_pos d₀.property.1
  have hNpos : 0 < N := Nat.ceil_pos.mpr (div_pos (by linarith) hd2)
  have htail (n : ℕ) (hn : N ≤ n) :
      (tapeMeasure (gapParameter true d)).real {ω | n < raceRounds neg pos L ω} ≤
          exp (-(d₀:ℝ)^2/2)^n := by
    have hnr : 3*U ≤ n*(d₀:ℝ)^2 := (div_le_iff₀ hd2).mp (Nat.ceil_le.mp hn)
    have hsv := positive_race_survival_of_fire neg pos weights hu j L hd h (hNpos.trans_le hn)
      (by linarith : U ≤ n*(d₀:ℝ)^2/3) (hfire n (by linarith)) hV
    rw [← exp_nat_mul]
    convert hsv using 1
    congr 1
    ring
  have hwork := geometric_work_bound (gapParameter true d) (raceRounds neg pos L) (2^L) N
    (raceRounds_le _ _ L) (measurable_raceRounds _ _ L) (exp_pos _).le
    (exp_lt_one_iff.mpr (by linarith : -(d₀:ℝ)^2/2 < 0)) htail
  have hi := inv_one_sub_exp_neg_le (show 0 < (d₀:ℝ)^2/2 by positivity)
  have hN : (N:ℝ) ≤ 3*U/(d₀:ℝ)^2+1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ 3*U/(d₀:ℝ)^2)).le
  have he : ((d₀:ℝ)^2/2)⁻¹ = 2/(d₀:ℝ)^2 := by field_simp
  rw [show -((d₀:ℝ)^2/2) = -(d₀:ℝ)^2/2 by ring, he] at hi
  apply hwork.trans
  have hh := add_le_add hN hi
  apply hh.trans
  apply (le_div_iff₀ hd2).mpr
  have hd2max : (d₀:ℝ)^2 ≤ 1/4 := by nlinarith [d₀.property.1, d₀.property.2]
  have hcancel : (3*U/(d₀:ℝ)^2+1+(1+2/(d₀:ℝ)^2))*(d₀:ℝ)^2 = 3*U+2*(d₀:ℝ)^2+2 := by
    field_simp [d₀.property.1.ne']
    ring
  rw [hcancel]
  nlinarith

/-- The full-null bank fires above the allowance at round `n` when
`z0 + (1 - z0) nullLaplace eta n` is at most `V`. -/
theorem fullNull_fire {z₀ : ℝ} (hz0 : 0 ≤ z₀) (hz1 : z₀ ≤ 1) (η : Measure Gap)
    [IsProbabilityMeasure η] (weights : ℕ → ℝ≥0) {u V : ℝ} (hu : 0 ≤ u) (j : ℕ) {n : ℕ}
    (hLap : z₀ + (1 - z₀) * nullLaplace η n ≤ V) (w : Fin n → Bool)
    (hw : (n:ℝ)/2 ≤ ∑ i, bit (w i))
    (hscore : V ≤ u*(weights j:ℝ)*exp (∑ i, positiveBitScore (EntropyTailQuantile.bandEdge j/4) (w i))) :
    fullNullBankTest z₀ η weights u n w := by
  have hs := (CriticalEntropy.streamProb_pos (1/2) (by norm_num) (by norm_num) w).le
  have hnull := (fullNull_prefix_gaussian hz0 hz1 η w hw).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hLap hs))
  exact fullNull_bank_of_score z₀ η weights hu j w hnull hscore

/-- The null Laplace transform is linear in the law. -/
theorem nullLaplace_smul (η : Measure Gap) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    nullLaplace (ENNReal.ofReal c • η) n = c * nullLaplace η n := by
  unfold nullLaplace
  rw [integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul]

/-- The work of the race with the full-null bank on a positive coin of gap
`d ≥ d₀`, for a reference gap `d₀` in band `j` and a design
`σ + τ + ζ = (1 - z₀) η`: the bound of the known-law theorem at `d₀`, with the
envelope `z₀ + threePieceEnvelope σ τ ζ d₀`. -/
theorem fullNull_positive_work {z₀ : ℝ} (hz0 : 0 ≤ z₀) (hz1 : z₀ ≤ 1) (η : Measure Gap)
    [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    [IsFiniteMeasure ζ] (hdesign : σ+τ+ζ = ENNReal.ofReal (1 - z₀) • η)
    (hσ : Integrable (fun x : Gap => (x:ℝ)⁻¹^2) σ)
    (hτ : Integrable (fun x : Gap => (x:ℝ)⁻¹) τ)
    (weights : ℕ → ℝ≥0) {ε ρ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ)
    (j L : ℕ) (hw : 0 < (weights j:ℝ)) (hw1 : (weights j:ℝ) ≤ 1)
    {d₀ d : Gap} (hd : d₀ ∈ EntropyTailQuantile.band j) (h : (d₀:ℝ) ≤ d) :
    conditionalRaceWork (negativeBankTest weights ε) (fullNullBankTest z₀ η weights (ρ*ε))
        L true d ≤
      12*positiveAllowance ε (weights j:ℝ) ρ (z₀ + threePieceEnvelope σ τ ζ d₀)/(d₀:ℝ)^2 := by
  have hV0 : 0 ≤ z₀ + threePieceEnvelope σ τ ζ d₀ :=
    add_nonneg hz0 (threePieceEnvelope_nonneg σ τ ζ d₀)
  have hLap (n : ℕ) (hn : 1 ≤ n*(d₀:ℝ)^2) :
      z₀ + (1 - z₀) * nullLaplace η n ≤ z₀ + threePieceEnvelope σ τ ζ d₀ := by
    have h3 := nullLaplace_three_piece σ τ ζ hσ hτ d₀ n hn
    rw [hdesign, nullLaplace_smul η (by linarith) n] at h3
    unfold threePieceEnvelope
    linarith
  have hr := positive_raceRounds_work_of_fire (negativeBankTest weights ε)
    (fullNullBankTest z₀ η weights (ρ*ε)) weights (mul_pos hρ hε).le
    (positiveAllowance_ge_one hε hε1 hw hw1) j L hd h
    (fun n hn w hhw hsc => fullNull_fire hz0 hz1 η weights (mul_pos hρ hε).le j (hLap n hn) w hhw hsc)
    (positiveAllowance_covers hε hw hρ hV0)
  unfold conditionalRaceWork
  simp only [raceCost, Nat.cast_mul, Nat.cast_ofNat]
  rw [integral_const_mul]
  have hm := mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 2)
  convert hm using 1
  ring

/-- The work of the race with the full-null bank on a coin of gap `d ≥ d₀`
with the sign law `q` at `d`. -/
theorem fullNull_mixture_work {z₀ : ℝ} (hz0 : 0 ≤ z₀) (hz1 : z₀ ≤ 1) (η : Measure Gap)
    [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    [IsFiniteMeasure ζ] (hdesign : σ+τ+ζ = ENNReal.ofReal (1 - z₀) • η)
    (hσ : Integrable (fun x : Gap => (x:ℝ)⁻¹^2) σ)
    (hτ : Integrable (fun x : Gap => (x:ℝ)⁻¹) τ)
    (weights : ℕ → ℝ≥0) {ε ρ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ)
    (j L : ℕ) (hw : 0 < (weights j:ℝ)) (hw1 : (weights j:ℝ) ≤ 1) (q : SignLaw)
    {d₀ d : Gap} (hd : d₀ ∈ EntropyTailQuantile.band j) (h : (d₀:ℝ) ≤ d) :
    mixtureRaceWork q (negativeBankTest weights ε) (fullNullBankTest z₀ η weights (ρ*ε)) L d ≤
      12*(d₀:ℝ)⁻¹^2*(1+Real.log (ε⁻¹)+Real.log ((weights j:ℝ)⁻¹))+
      12*q.val d*(d₀:ℝ)⁻¹^2*logPlus ((z₀ + threePieceEnvelope σ τ ζ d₀)/ρ) := by
  let B := 12*(d₀:ℝ)⁻¹^2*(1+Real.log (ε⁻¹)+Real.log ((weights j:ℝ)⁻¹))
  let S := (d₀:ℝ)⁻¹^2*logPlus ((z₀ + threePieceEnvelope σ τ ζ d₀)/ρ)
  have hb : 0 ≤ 1+Real.log (ε⁻¹)+Real.log ((weights j:ℝ)⁻¹) := by
    have he := Real.log_nonneg ((one_le_inv₀ hε).mpr hε1)
    have hw' := Real.log_nonneg ((one_le_inv₀ hw).mpr hw1)
    linarith
  have hp : conditionalRaceWork (negativeBankTest weights ε)
      (fullNullBankTest z₀ η weights (ρ*ε)) L true d ≤ B+12*S := by
    have h' := fullNull_positive_work hz0 hz1 η σ τ ζ hdesign hσ hτ weights hε hε1 hρ j L hw hw1
      hd h
    apply h'.trans_eq
    dsimp [B, S, positiveAllowance, logPlus]
    ring
  have hn : conditionalRaceWork (negativeBankTest weights ε)
      (fullNullBankTest z₀ η weights (ρ*ε)) L false d ≤ B := by
    have h' := race_negative_work_of_le (fullNullBankTest z₀ η weights (ρ*ε)) weights hε hε1 j L
      hw hw1 hd h
    rw [log_inverse_product hε hw] at h'
    apply h'.trans
    have he : (3/(2*(d₀:ℝ)^2))*(1+(Real.log (ε⁻¹)+Real.log ((weights j:ℝ)⁻¹))) =
        (3/2)*((d₀:ℝ)⁻¹^2*(1+Real.log (ε⁻¹)+Real.log ((weights j:ℝ)⁻¹))) := by ring
    rw [he]
    dsimp [B]
    nlinarith only [mul_nonneg (sq_nonneg ((d₀:ℝ)⁻¹)) hb]
  have hp' := mul_le_mul_of_nonneg_left hp (q.property.2 d).1
  have hn' := mul_le_mul_of_nonneg_left hn (sub_nonneg.mpr (q.property.2 d).2)
  unfold mixtureRaceWork
  dsimp [B, S] at hp' hn'
  nlinarith only [hp', hn']

end ThresholdHC.FullNullBank
