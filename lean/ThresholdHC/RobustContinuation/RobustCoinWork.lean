import ThresholdHC.RobustContinuation.RaceOrder
import ThresholdHC.EntropyTailUpper.BankWork

/-! The work of the race on a coin with a larger gap than the reference gap.

Increasing a gap can remove a wrong early exit, so the stopping time of the
race is not monotone in the flips. Its work bounds still hold at the
reference gap `d₀` for a coin of every gap `d ≥ d₀`:

* the ordinary work kernel `min{M, 17 d⁻² (1 + log₊(M d²))}` decreases with
  the gap;
* for a negative coin, the race stops by the crossing time of the matching
  negative reference, whose drift increases with the gap;
* for a positive coin, the race has stopped once the running mean of the
  bank's flips is above `1/2 + d₀/2`, which is an upper set of tapes, so
  surviving is at most as likely as for the coin of gap `d₀`.

The three bounds are those of the known-law theorem with `d₀` in place of
the gap of the coin. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal NNReal BigOperators

namespace ThresholdHC.RobustContinuation
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.Uniform713 ThresholdHC.BlindUpper ThresholdHC.EntropyTailUpper

/-- The ordinary work kernel does not increase with the gap. -/
theorem ordinaryWorkKernel_antitone_gap {M : ℝ} (hM : 0 < M) {d d' : Gap} (h : (d:ℝ) ≤ d') :
    ordinaryWorkKernel M (d':ℝ) ≤ ordinaryWorkKernel M (d:ℝ) := by
  have hd := d.property.1
  have hd' := d'.property.1
  have hx : 0 < (d:ℝ)^2 := by positivity
  have hy : 0 < (d':ℝ)^2 := by positivity
  have hxy : (d:ℝ)^2 ≤ (d':ℝ)^2 := pow_le_pow_left₀ hd.le h 2
  have hratio : 1 ≤ (d':ℝ)^2/(d:ℝ)^2 := (one_le_div hx).mpr hxy
  have hA0 : 0 ≤ max 0 (log (M*(d:ℝ)^2)) := le_max_left _ _
  have hlog : log (M*(d':ℝ)^2) ≤ log (M*(d:ℝ)^2) + ((d':ℝ)^2/(d:ℝ)^2 - 1) := by
    have he : M*(d':ℝ)^2 = (M*(d:ℝ)^2) * ((d':ℝ)^2/(d:ℝ)^2) := by field_simp
    rw [he, log_mul (by positivity) (by positivity)]
    linarith [log_le_sub_one_of_pos (show 0 < (d':ℝ)^2/(d:ℝ)^2 by positivity)]
  have hB : 1 + max 0 (log (M*(d':ℝ)^2)) ≤
      (d':ℝ)^2/(d:ℝ)^2 * (1 + max 0 (log (M*(d:ℝ)^2))) := by
    have h1 : max 0 (log (M*(d':ℝ)^2)) ≤
        max 0 (log (M*(d:ℝ)^2)) + ((d':ℝ)^2/(d:ℝ)^2 - 1) :=
      max_le (by linarith) (hlog.trans (by linarith [le_max_right 0 (log (M*(d:ℝ)^2))]))
    nlinarith [mul_nonneg (sub_nonneg.mpr hratio) hA0]
  unfold ordinaryWorkKernel
  refine min_le_min le_rfl ?_
  calc 17*(d':ℝ)⁻¹^2*(1+max 0 (log (M*(d':ℝ)^2)))
      ≤ 17*(d':ℝ)⁻¹^2*((d':ℝ)^2/(d:ℝ)^2 * (1 + max 0 (log (M*(d:ℝ)^2)))) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ = 17*(d:ℝ)⁻¹^2*(1+max 0 (log (M*(d:ℝ)^2))) := by field_simp

/-- The work of any race on a coin of gap `d ≥ d₀` is at most twice the
ordinary work kernel at `d₀`. -/
theorem race_work_le_ordinary_of_le (neg pos : PrefixTest) (L : ℕ) (s : Bool) {d₀ d : Gap}
    (h : (d₀:ℝ) ≤ d) :
    (∫ ω, (raceCost neg pos L ω : ℝ) ∂tapeMeasure (gapParameter s d)) ≤
      2*ordinaryWorkKernel (cap L) (d₀:ℝ) :=
  (race_expected_work_le_ordinary neg pos L d s).trans
    (mul_le_mul_of_nonneg_left (ordinaryWorkKernel_antitone_gap (cap_pos L) h) (by norm_num))

/-- The drift of a negative reference score increases with the gap of the
coin. -/
theorem negativeReferenceDrift_mono {d d' r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) (h : d ≤ d') :
    negativeReferenceDrift d r ≤ negativeReferenceDrift d' r := by
  unfold negativeReferenceDrift
  have hl : log (1-2*r) ≤ log (1+2*r) := log_le_log (by linarith) (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hl)]

/-- The crossing time of a negative reference matched to `d₀`, under a
negative coin of gap `d ≥ d₀`. -/
theorem negative_scoreStop_work_of_le {d₀ d : Gap} (h : (d₀:ℝ) ≤ d) {r b : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1/4) (hdr : (d₀:ℝ)/2 ≤ r) (hrd : r ≤ (d₀:ℝ)) (hb : 0 ≤ b) (M : ℕ) :
    (∫ ω, (scoreStop (negativeBitScore r) b M ω : ℝ) ∂tapeMeasure (gapParameter false d)) ≤
      (3/(4*(d₀:ℝ)^2))*(1+b) := by
  have hw := scoreStop_expected_mul_drift_le (gapParameter false d) (negativeBitScore r)
    hb (by norm_num : (0:ℝ) ≤ 1) (negativeBitScore_le_one hr0 hr1) M
  rw [negativeBitScore_mean] at hw
  have hm := (negativeReferenceDrift_lower d₀.property.1.le hr0 hr1 hdr hrd).trans
    (negativeReferenceDrift_mono hr0 hr1 h)
  have hn : 0 ≤ ∫ ω, (scoreStop (negativeBitScore r) b M ω : ℝ)
      ∂tapeMeasure (gapParameter false d) := integral_nonneg (fun _ => Nat.cast_nonneg _)
  have hs := mul_le_mul_of_nonneg_left hm hn
  have hd2 : 0 < (d₀:ℝ)^2 := sq_pos_of_pos d₀.property.1
  calc
    _ ≤ (3*(1+b))/(4*(d₀:ℝ)^2) := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
    _ = _ := by ring

/-- The work of the bank race on a negative coin of gap `d ≥ d₀`, for a
reference gap `d₀` in band `j`. -/
theorem bank_race_negative_work_of_le (μ : Measure Gap) (weights : ℕ → ℝ≥0) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (u : ℝ) (j L : ℕ) (hw : 0 < (weights j:ℝ))
    (hw1 : (weights j:ℝ) ≤ 1) {d₀ d : Gap} (hd : d₀ ∈ EntropyTailQuantile.band j)
    (h : (d₀:ℝ) ≤ d) :
    (∫ ω, (raceCost (negativeBankTest weights ε) (positiveBankTest μ weights u) L ω : ℝ)
      ∂tapeMeasure (gapParameter false d)) ≤
      (3/(2*(d₀:ℝ)^2))*(1+log (ε*(weights j:ℝ))⁻¹) := by
  let f := negativeBitScore (EntropyTailQuantile.bandEdge j/2)
  let b := log (ε*(weights j:ℝ))⁻¹
  have hi := (parityTape_measurePreserving 0 (gapParameter false d)).integrable_comp_of_integrable
    (integrable_scoreStop (gapParameter false d) f b (2^L))
  have hle := integral_mono (integrable_raceCost _ _ L _) (hi.const_mul 2)
    (fun ω => show (raceCost _ _ L ω : ℝ) ≤ 2*(scoreStop f b (2^L) (parityTape 0 ω) : ℝ) by
      exact_mod_cast Nat.mul_le_mul_left 2 (bank_raceRounds_le_score μ weights hε u j L hw ω))
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
  calc
    _ ≤ 2*(∫ ω, (scoreStop f b (2^L) ω : ℝ) ∂tapeMeasure (gapParameter false d)) := hle
    _ ≤ 2*((3/(4*(d₀:ℝ)^2))*(1+b)) := mul_le_mul_of_nonneg_left hwk (by norm_num)
    _ = _ := by dsimp [b]; ring

/-- The running mean of a prefix is monotone in the flips. -/
theorem prefixMean_mono (n : ℕ) {ω ω' : ℕ → Bool} (h : ω ≤ ω') :
    prefixMean observations n ω ≤ prefixMean observations n ω' := by
  unfold prefixMean
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun i _ => bit_mono (h i)) (Nat.cast_nonneg n)

/-- Survival of the bank race on a positive coin of gap `d ≥ d₀`, for a
reference gap `d₀` in band `j`: the bound of the coin of gap `d₀`. -/
theorem positive_race_survival_of_le (μ : Measure Gap) [IsProbabilityMeasure μ]
    (weights : ℕ → ℝ≥0) (ε : ℝ) {u V U : ℝ} (hu : 0 ≤ u)
    (j L : ℕ) {d₀ d : Gap} (hd : d₀ ∈ EntropyTailQuantile.band j) (h : (d₀:ℝ) ≤ d)
    {n : ℕ} (hn : 0 < n) (hU : U ≤ n*(d₀:ℝ)^2/3)
    (hLap : nullLaplace μ n ≤ V) (hV : V ≤ u*(weights j:ℝ)*exp U) :
    (tapeMeasure (gapParameter true d)).real
      {ω | n < raceRounds (negativeBankTest weights ε) (positiveBankTest μ weights u) L ω} ≤
        exp (-(n:ℝ)*(d₀:ℝ)^2/2) := by
  let bad := {ω | (d₀:ℝ)/2 ≤ (gapParameter true d₀:ℝ)-prefixMean observations n ω}
  have hbadm : MeasurableSet bad := measurableSet_le measurable_const
    (measurable_const.sub (measurable_prefixMean measurable_observations n))
  have hs : {ω | n < raceRounds (negativeBankTest weights ε) (positiveBankTest μ weights u) L ω} ⊆
      parityTape 0 ⁻¹' bad := by
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
    have hnull := (null_prefix_gaussian_ennreal μ (tapePrefix n (parityTape 0 ω)) hc).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hLap
        (CriticalEntropy.streamProb_pos (1/2) (by norm_num) (by norm_num) _).le))
    have hhit := positive_bank_of_score μ weights hu j (tapePrefix n (parityTape 0 ω)) hnull
      (hV.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (hU.trans hscore))
        (mul_nonneg hu (weights j).property)))
    exact (not_le_of_gt hnω) (raceRounds_le_bank _ _ L n ω (Or.inr hhit))
  have h1 := measureReal_mono (μ := tapeMeasure (gapParameter true d)) hs
  rw [parityTape_event 0 _ (E := bad) hbadm] at h1
  -- A low running mean is a lower set, so it is less likely under the larger coin.
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

/-- The number of rounds of the bank race on a positive coin of gap
`d ≥ d₀`, for a reference gap `d₀` in band `j`. -/
theorem positive_raceRounds_work_of_le (μ : Measure Gap) [IsProbabilityMeasure μ]
    (weights : ℕ → ℝ≥0) (ε : ℝ) {u V U : ℝ} (hu : 0 ≤ u) (hU : 1 ≤ U)
    (j L : ℕ) {d₀ d : Gap} (hd : d₀ ∈ EntropyTailQuantile.band j) (h : (d₀:ℝ) ≤ d)
    (hLap : ∀ n : ℕ, 1 ≤ n*(d₀:ℝ)^2 → nullLaplace μ n ≤ V)
    (hV : V ≤ u*(weights j:ℝ)*exp U) :
    (∫ ω, (raceRounds (negativeBankTest weights ε) (positiveBankTest μ weights u) L ω : ℝ)
      ∂tapeMeasure (gapParameter true d)) ≤ 6*U/(d₀:ℝ)^2 := by
  let N : ℕ := ⌈3*U/(d₀:ℝ)^2⌉₊
  have hd2 : 0 < (d₀:ℝ)^2 := sq_pos_of_pos d₀.property.1
  have hNpos : 0 < N := Nat.ceil_pos.mpr (div_pos (by linarith) hd2)
  have htail (n : ℕ) (hn : N ≤ n) :
      (tapeMeasure (gapParameter true d)).real
        {ω | n < raceRounds (negativeBankTest weights ε) (positiveBankTest μ weights u) L ω} ≤
          exp (-(d₀:ℝ)^2/2)^n := by
    have hnr : 3*U ≤ n*(d₀:ℝ)^2 := (div_le_iff₀ hd2).mp (Nat.ceil_le.mp hn)
    have hsv := positive_race_survival_of_le μ weights ε hu j L hd h (hNpos.trans_le hn)
      (by linarith : U ≤ n*(d₀:ℝ)^2/3) (hLap n (by linarith)) hV
    rw [← exp_nat_mul]
    convert hsv using 1
    congr 1
    ring
  have hwork := geometric_work_bound (gapParameter true d)
    (raceRounds (negativeBankTest weights ε) (positiveBankTest μ weights u) L) (2^L) N
    (raceRounds_le _ _ L) (measurable_raceRounds _ _ L) (exp_pos _).le
    (exp_lt_one_iff.mpr (by linarith : -(d₀:ℝ)^2/2 < 0)) htail
  have hi := inv_one_sub_exp_neg_le (show 0 < (d₀:ℝ)^2/2 by positivity)
  have hN : (N:ℝ) ≤ 3*U/(d₀:ℝ)^2+1 := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 3*U/(d₀:ℝ)^2)).le
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

/-- The work of the bank race on a positive coin of gap `d ≥ d₀`, for a
reference gap `d₀` in band `j`, with the three-piece surcharge at `d₀`. -/
theorem bank_race_positive_work_of_le (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    (hσ : Integrable (fun x : Gap => (x:ℝ)⁻¹^2) σ)
    (hτ : Integrable (fun x : Gap => (x:ℝ)⁻¹) τ)
    (weights : ℕ → ℝ≥0) {ε ρ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ)
    (j L : ℕ) (hw : 0 < (weights j:ℝ)) (hw1 : (weights j:ℝ) ≤ 1)
    {d₀ d : Gap} (hd : d₀ ∈ EntropyTailQuantile.band j) (h : (d₀:ℝ) ≤ d) :
    (∫ ω, (raceCost (negativeBankTest weights ε) (positiveBankTest (σ+τ+ζ) weights (ρ*ε)) L ω : ℝ)
      ∂tapeMeasure (gapParameter true d)) ≤
      12*positiveAllowance ε (weights j:ℝ) ρ (threePieceEnvelope σ τ ζ d₀)/(d₀:ℝ)^2 := by
  have hr := positive_raceRounds_work_of_le (σ+τ+ζ) weights ε (mul_pos hρ hε).le
    (positiveAllowance_ge_one hε hε1 hw hw1) j L hd h
    (fun n hn => nullLaplace_three_piece σ τ ζ hσ hτ d₀ n hn)
    (positiveAllowance_covers hε hw hρ (threePieceEnvelope_nonneg σ τ ζ d₀))
  simp only [raceCost, Nat.cast_mul, Nat.cast_ofNat]
  rw [integral_const_mul]
  have hm := mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 2)
  dsimp only [threePieceEnvelope]
  convert hm using 1
  ring

end ThresholdHC.RobustContinuation
