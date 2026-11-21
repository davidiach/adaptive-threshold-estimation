import ThresholdHC.BiasAudit.Specification
import ThresholdHC.BiasAudit.Measure

/-! The counterexample of `proposals/constants/BIAS_AUDIT.md:49-69`. For the grid
winner `(k1,k2) = (1/4,1/2)`, positive sign, `d = 1/10` and cap `N = 2^97`, every tape
whose first `128` flips are tails stops negatively by the prefix `n = 128 = 2^7`. That
cylinder has probability `(2/5)^128`, which exceeds `2907` times the v4 envelope
`(N d²)^{-2} = 10000/2^194`. -/
noncomputable section
namespace ThresholdHC.BiasAudit
open MeasureTheory ProbabilityTheory Real
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Uniform713

/-- The frozen threshold at dyadic prefixes, with the logarithm of the cap ratio
expanded. -/
theorem finiteBoundary_eq_log_two (k1 k2 : ℝ) {j L : ℕ} (hjL : j ≤ L) :
    finiteBoundary k1 k2 j L =
      Real.sqrt ((k1 + k2 * (((L - j : ℕ) : ℝ) * Real.log 2)) / (2 : ℝ) ^ j) := by
  unfold finiteBoundary thrK
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have h : (2 : ℝ) ^ L / 2 ^ j = 2 ^ (L - j) := by
    rw [pow_sub₀ (2 : ℝ) two_ne_zero hjL, div_eq_mul_inv]
  rw [h, Real.log_pow]

/-- At the prefix `n = 2^7` with cap `N = 2^97`, the grid-winner threshold is below
`1/2`: `n t(n,N)² = 1/4 + 45 log 2 < 32 = n/4`. -/
theorem gridWinner_threshold_lt : finiteBoundary (1/4) (1/2) 7 97 < 1/2 := by
  rw [finiteBoundary_eq_log_two _ _ (by norm_num : 7 ≤ 97),
    Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1/2)]
  have h := Real.log_two_lt_d9
  have h90 : (((97 - 7 : ℕ) : ℝ)) = 90 := by norm_num
  rw [h90, div_lt_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 7)]
  norm_num at h ⊢
  linarith

/-- The cylinder of tapes whose first `128` flips are all tails. -/
def tailsCylinder : Set (ℕ → Bool) := tapePrefix 128 ⁻¹' {fun _ => false}

theorem tailsCylinder_apply {ω : ℕ → Bool} (hω : ω ∈ tailsCylinder) {i : ℕ}
    (hi : i < 128) : ω i = false := by
  have h : tapePrefix 128 ω = fun _ => false := hω
  exact congrFun h ⟨i, hi⟩

/-- On the tails cylinder every inspected dyadic mean up to `2^7` is zero. -/
theorem dyadicMean_tails {ω : ℕ → Bool} (hω : ω ∈ tailsCylinder) {j : ℕ} (hj : j ≤ 7) :
    dyadicMean observations j ω = 0 := by
  unfold dyadicMean prefixMean
  rw [Finset.sum_eq_zero, zero_div]
  intro i hi
  have hi' : i < 2 ^ j := Finset.mem_range.mp hi
  have h2 : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hj
  have hω' : ω i = false := tailsCylinder_apply hω (by omega)
  simp [observations, bit, hω']

/-- On the tails cylinder the grid-winner classifier with cap `2^97` outputs `0`. -/
theorem gridWinner_decision_tails {ω : ℕ → Bool} (hω : ω ∈ tailsCylinder) :
    firstDecision (finiteBoundary (1/4) (1/2)) (fun j => dyadicMean observations j ω) 97 =
      0 := by
  have hcross : finiteBoundary (1/4) (1/2) 7 97 <
      |(fun j => dyadicMean observations j ω) 7 - 1/2| := by
    simp only [dyadicMean_tails hω le_rfl]
    rw [zero_sub, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
    exact gridWinner_threshold_lt
  have hstop := firstStop_le_of_cross (finiteBoundary (1/4) (1/2))
    (fun j => dyadicMean observations j ω) 97 7 hcross
  unfold firstDecision
  beta_reduce
  rw [dyadicMean_tails hω hstop]
  norm_num

/-- The tails cylinder has tape probability `(1-p)^128`. -/
theorem tailsCylinder_prob (p : unitInterval) :
    (tapeMeasure p).real tailsCylinder = (1 - (p : ℝ)) ^ 128 := by
  unfold tailsCylinder
  rw [← map_measureReal_apply (measurable_prefix 128) (measurableSet_singleton _),
    prefix_map, finiteMeasure_real_singleton]
  simp [streamProb, Finset.prod_const]

theorem gridWinner_error_lower :
    (2/5 : ℝ) ^ 128 ≤ errProbK (1/4) (1/2) 97 (1/10) true := by
  rw [errProbK_eq_measure_gen (1/4) (1/2) 97 (1/10) true (by norm_num) (by norm_num)]
  have hp : (2/5 : ℝ) = 1 - (coinParameter (1/10) true (by norm_num) (by norm_num) : ℝ) := by
    rw [coinParameter_val]
    norm_num [coinP]
  rw [hp, ← tailsCylinder_prob]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq]
  rw [gridWinner_decision_tails hω]
  norm_num [bit]

theorem gridWinner_envelope_small :
    2907 * min 1 ((((2 : ℝ) ^ 97 * (1/10) ^ 2)⁻¹) ^ 2) < (2/5 : ℝ) ^ 128 := by
  calc
    2907 * min 1 ((((2 : ℝ) ^ 97 * (1/10) ^ 2)⁻¹) ^ 2) ≤
        2907 * ((((2 : ℝ) ^ 97 * (1/10) ^ 2)⁻¹) ^ 2) := by
      gcongr
      exact min_le_right _ _
    _ < (2/5 : ℝ) ^ 128 := by norm_num

theorem gridWinnerCounterexample : GridWinnerCounterexampleStatement :=
  ⟨gridWinner_error_lower, gridWinner_envelope_small⟩

private theorem envelope_contradiction {a e m : ℝ} (h1 : a ≤ e) (h : e ≤ m)
    (h2 : 2907 * m < a) (hm : 0 ≤ m) : False := by
  linarith

theorem gridWinnerFailsEnvelope : GridWinnerFailsEnvelopeStatement := by
  intro h
  exact envelope_contradiction gridWinner_error_lower
    (h 97 (1/10) true (by norm_num) (by norm_num)) gridWinner_envelope_small
    (le_min zero_le_one (sq_nonneg _))

end ThresholdHC.BiasAudit
