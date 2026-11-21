import ThresholdHC.StoppedTimeUniform.Specification
import ThresholdHC.ConfidenceProgram.Lower
import ThresholdHC.ConfidenceEntropy.Full
import ThresholdHC.HardBudget.SelectionScale
import ThresholdHC.Anytime.Width

/-! The fixed-budget confidence chain for estimates formed from the seed and
the first `n` physical observations, and the time-uniform remark.

The chain is the one of `ConfidenceProgram.quartet_confidence` and
`ConfidenceEntropy.closed_quantile_confidence_lower`. Only the testing step
changes: the two smoothed priors are compared through their laws on the
observed prefix, whose KL divergence is at most `(8/3) κ` times the expected
work of the prefix (`observable_reference_work_kl`), and that work is at most
`n` (`prefix_expected_work_le`). -/
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.StoppedTimeUniform
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.AnytimeLower
open ThresholdHC.Genie ThresholdHC.StoppingProgram ThresholdHC.ConfidenceTransfer
open ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceProgram

/-- Uniform confidence for a prefix estimate at a radius below a quarter of a
pair's separation costs logarithmic information within `n` observations. -/
theorem prefix_pair_work {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) {n : ℕ} (H : R × Prefix n → ℝ)
    (hH : Measurable H) (q r : SignLaw) {ρ κ ε δ : ℝ} (hκ : 0 ≤ κ) (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hq : RarePrior μ ρ q) (hr : RarePrior μ ρ r)
    (hloc : LocalReferenceWorkBound μ (gapParameter false) (gapParameter true)
      (signUnit q) (signUnit r) κ)
    (hconf : ∀ s : SignLaw, RarePrior μ ρ s →
      (observablePrefixLaw μ A s n) {x | ε < |H x - signMean μ s.val|} ≤ ENNReal.ofReal δ)
    (hsep : 4*ε < signMean μ q.val - signMean μ r.val) :
    Real.log (1/δ)/4 ≤ (8/3)*κ*n := by
  let s := smoothedSign q r
  let t := smoothedSign r q
  have hs := smoothedSign_rare μ q r hq hr
  have ht := smoothedSign_rare μ r q hr hq
  have hsep' : 2*ε < signMean μ s.val-signMean μ t.val := by
    rw [smoothedSign_separation μ r q]
    linarith
  have htest := ThresholdHC.Confidence.confidence_testing_bound (observablePrefixLaw μ A s n)
    (observablePrefixLaw μ A t n) H hH _ _ ε δ hδ hδ' hsep' (hconf s hs) (hconf t ht)
  have hu := observable_reference_work_kl μ A q r n κ hκ hloc
  have hwork := prefix_expected_work_le μ A s n
  have hu' : klDiv (observablePrefixLaw μ A s n) (observablePrefixLaw μ A t n) ≤
      ENNReal.ofReal ((8/3)*κ*n) :=
    hu.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hwork (mul_nonneg (by norm_num) hκ)))
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg (by norm_num) hκ)
    (Nat.cast_nonneg n))).mp (htest.trans hu')

/-- Every four-prior certificate bounds the radius of a uniformly confident
prefix estimate, at the effective budget `n / log(1/δ)`. -/
theorem prefix_quartet_confidence {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) {n : ℕ} (H : R × Prefix n → ℝ)
    (hH : Measurable H) {ρ δ ε : ℝ} (hn : 0 < n) (hδ : 0 < δ) (hu : δ ≤ 1/4)
    (hc : ∀ q : SignLaw, RarePrior μ ρ q →
      (observablePrefixLaw μ A q n) {x | ε < |H x - signMean μ q.val|} ≤ ENNReal.ofReal δ)
    (Q : FourPriors) (hQ : Admissible μ ρ Q) :
    infiniteDualRatio μ ((n : ℝ)/Real.log (1/δ)) Q ≤ ENNReal.ofReal ((30*ε)^2) := by
  let B : ℝ := n
  have hB : 0 < B := Nat.cast_pos.mpr hn
  let ℓ := Real.log (1/δ)
  have hℓ : 0 < ℓ := ThresholdHC.Confidence.confidence_log_pos hδ hu
  let β := B/ℓ
  have hβ : 0 < β := div_pos hB hℓ
  change infiniteDualRatio μ β Q ≤ _
  by_cases htop : infiniteInformationRatio μ Q = ⊤
  · simp [infiniteDualRatio,htop,(ENNReal.ofReal_pos.mpr hβ).ne']
  let Δ := signMean μ Q.high.val-signMean μ Q.low.val
  by_cases hzero : Δ ≤ 0
  · simp [infiniteDualRatio,show ENNReal.ofReal (signMean μ Q.high.val-signMean μ Q.low.val) = 0
      from ENNReal.ofReal_eq_zero.mpr hzero]
  have hΔ : 0 < Δ := lt_of_not_ge hzero
  let K := (infiniteInformationRatio μ Q).toReal
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hKeq := ENNReal.ofReal_toReal htop
  let v := 1+6*β*K
  have hv1 : 1 ≤ v := by dsimp [v]; nlinarith [mul_nonneg hβ.le hK]
  let c := Real.sqrt v
  have hc1 : 1 ≤ c := Real.one_le_sqrt.mpr hv1
  have hc0 : 0 < c := by linarith
  have hc2 : c^2 = v := Real.sq_sqrt (by linarith)
  let a := 1/c
  have ha : 0 < a := one_div_pos.mpr hc0
  have ha1 : a ≤ 1 := (div_le_one hc0).2 hc1
  have hac : a*c = 1 := div_mul_cancel₀ _ hc0.ne'
  have hav : a^2*(1+6*β*K) = 1 := by change a^2*v = 1; rw [← hc2,← mul_pow,hac,one_pow]
  let q := absorbedLow Q
  let r := absorbedHigh Q
  let q' := contractPrior q r a ⟨ha.le,ha1⟩
  let r' := contractPrior r q a ⟨ha.le,ha1⟩
  have had := absorbedPriors_admissible μ Q hQ
  have hq := contractPrior_rare μ q r had.1 had.2.1 a ⟨ha.le,ha1⟩
  have hr := contractPrior_rare μ r q had.2.1 had.1 a ⟨ha.le,ha1⟩
  have hsep : signMean μ r'.val-signMean μ q'.val = a*(Δ/3) := by
    rw [show signMean μ r'.val-signMean μ q'.val = a*(signMean μ r.val-signMean μ q.val) from
      contractPrior_gap μ q r a ⟨ha.le,ha1⟩]
    have h := absorbedPriors_gap μ Q
    change signMean μ r.val-signMean μ q.val = (1/3)*Δ at h
    rw [h]; ring
  have hprice (m : ℕ) : informationRatio μ m (midpointFourPriors q' r') ≤ ENNReal.ofReal (a^2*K) := by
    rw [show informationRatio μ m (midpointFourPriors q' r') = _ from
      contractPrior_informationRatio μ m q r a ⟨ha.le,ha1⟩,ENNReal.ofReal_mul (sq_nonneg a)]
    exact mul_le_mul_right ((absorbedPriors_informationRatio_le μ m Q).trans
      ((informationRatio_le_infinite μ m Q).trans_eq hKeq.symm)) _
  have hl : LocalReferenceWorkBound μ (gapParameter false) (gapParameter true)
      (signUnit r') (signUnit q') (a^2*K/2) :=
    midpoint_reference_bound μ q' r' (mul_nonneg (sq_nonneg _) hK) hprice
  have hsmall : a*Δ ≤ 12*ε := by
    by_contra! hx
    have h := prefix_pair_work μ A H hH r' q' (by positivity : 0 ≤ a^2*K/2)
      hδ hu hr hq hl hc (by rw [hsep]; linarith)
    change ℓ/4 ≤ (8/3)*(a^2*K/2)*B at h
    have hB' : β*ℓ = B := div_mul_cancel₀ _ hℓ.ne'
    rw [← hB'] at h
    have hs : a^2*K*β ≤ 1/6 := by nlinarith only [hav,sq_nonneg a]
    nlinarith only [h,mul_le_mul_of_nonneg_right hs hℓ.le,hℓ]
  have hd : Δ ≤ (12*ε)*c := by
    have h := mul_le_mul_of_nonneg_right hsmall hc0.le
    calc Δ = (a*Δ)*c := by rw [mul_comm a Δ,mul_assoc,hac,mul_one]
         _ ≤ _ := h
  have hgap := pow_le_pow_left₀ hΔ.le hd 2
  rw [mul_pow,hc2] at hgap
  have hpos : 0 < 4+β*K := by positivity
  have hfactor : 144*v ≤ 900*(4+β*K) := by dsimp [v]; nlinarith only [mul_nonneg hβ.le hK]
  have hdiv : Δ^2/(4+β*K) ≤ (30*ε)^2 := (div_le_iff₀ hpos).2
    (by nlinarith only [hgap,mul_le_mul_of_nonneg_right hfactor (sq_nonneg ε)])
  have hden : 4+ENNReal.ofReal β*infiniteInformationRatio μ Q = ENNReal.ofReal (4+β*K) := by
    rw [← hKeq,← ENNReal.ofReal_mul hβ.le,← ENNReal.ofReal_ofNat 4,
      ← ENNReal.ofReal_add (by norm_num) (mul_nonneg hβ.le hK)]
  change ENNReal.ofReal Δ ^2/(4+ENNReal.ofReal β*infiniteInformationRatio μ Q) ≤ _
  rw [hden,← ENNReal.ofReal_pow hΔ.le,← ENNReal.ofReal_div_of_pos hpos]
  exact ENNReal.ofReal_le_ofReal hdiv

/-- The stopping-program value at `n / log(1/δ)` bounds the radius of every
uniformly confident prefix estimate. -/
theorem prefix_program_lower {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) {n : ℕ} (H : R × Prefix n → ℝ)
    (hH : Measurable H) {ρ δ ε : ℝ} (hr : 0 < ρ) (hr' : ρ ≤ 1/2) (hn : 0 < n)
    (hd : 0 < δ) (hd' : δ ≤ 1/4) (hε : 0 ≤ ε)
    (hc : ∀ q : SignLaw, RarePrior μ ρ q →
      (observablePrefixLaw μ A q n) {x | ε < |H x - signMean μ q.val|} ≤ ENNReal.ofReal δ) :
    infiniteProgramValue μ ρ ((n : ℝ)/Real.log (1/δ))/30 ≤ ENNReal.ofReal ε := by
  have hβ : 0 < (n : ℝ)/Real.log (1/δ) :=
    div_pos (Nat.cast_pos.mpr hn) (ThresholdHC.Confidence.confidence_log_pos hd hd')
  have h : infiniteProgramValue μ ρ ((n : ℝ)/Real.log (1/δ)) ^2 ≤ ENNReal.ofReal ((30*ε)^2) := by
    rw [(infinite_four_prior_duality μ hr hr' hβ).1]
    apply iSup_le; intro Q; apply iSup_le; intro hQ
    exact prefix_quartet_confidence μ A H hH hn hd hd' hc Q hQ
  have hroot := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 1/2)
  rw [← ENNReal.rpow_two,← ENNReal.rpow_mul,ofReal_square_rpow_half (30*ε) (by positivity),
    ENNReal.ofReal_mul (by norm_num : 0 ≤ (30:ℝ))] at hroot
  apply (ENNReal.div_le_iff (by norm_num : (30:ℝ≥0∞) ≠ 0) (by norm_num : (30:ℝ≥0∞) ≠ ⊤)).2
  simpa [mul_comm] using hroot

/-- The explicit fixed-budget coefficient for prefix estimates. -/
theorem prefix_confidence_explicit {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) {n : ℕ} (H : R × Prefix n → ℝ)
    (hH : Measurable H) {ρ δ ε : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hn : 0 < n)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1/4) (hε : 0 ≤ ε)
    (hc : ∀ q : SignLaw, RarePrior μ ρ q →
      (observablePrefixLaw μ A q n) {x | ε < |H x - signMean μ q.val|} ≤ ENNReal.ofReal δ) :
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17) *
        ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ)/Real.log (1/δ)) ≤ ENNReal.ofReal ε := by
  have hβ : 0 < (n : ℝ)/Real.log (1/δ) :=
    div_pos (Nat.cast_pos.mpr hn) (ThresholdHC.Confidence.confidence_log_pos hδ hδ4)
  have hp := ThresholdHC.ConfidenceEntropy.closed_quantile_program μ hρ hρ4 hβ
  have hl := prefix_program_lower μ A H hH hρ (by linarith) hn hδ hδ4 hε hc
  have hq : ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 17) *
      ThresholdHC.EntropyTailQuantile.closedQuantileValue μ ρ ((n : ℝ)/Real.log (1/δ)) ≤
        ENNReal.ofReal ε := by
    apply le_trans ?_ hl
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num : (30 : ℝ≥0∞) ≠ 0))
      (Or.inl (by norm_num : (30 : ℝ≥0∞) ≠ ∞))).mpr
    calc
      _ = ENNReal.ofReal (30*(10 : ℝ)⁻¹^17) *
          ThresholdHC.EntropyTailQuantile.closedQuantileValue μ ρ ((n : ℝ)/Real.log (1/δ)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 30),ENNReal.ofReal_ofNat]
        ring
      _ ≤ _ := hp
  exact (mul_le_mul' le_rfl
    (ThresholdHC.EntropyTail.selection_quantile_comparison μ hρ hρ4 hβ).1).trans hq

/-- Joint coverage at level `1 - δ` bounds the failure probability of the
midpoint at each budget. -/
theorem coverage_prefix_failure {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (L U : ∀ n, R × Prefix n → ℝ)
    (hL : ∀ n, Measurable (L n)) (hU : ∀ n, Measurable (U n)) {ρ δ : ℝ} (t : ℕ → ℝ)
    (hc : OnlineIntervalCoverage μ A L U ρ δ t) (n : ℕ) (q : SignLaw) (hq : RarePrior μ ρ q) :
    (observablePrefixLaw μ A q n) {x | t n < |(L n x + U n x)/2 - signMean μ q.val|} ≤
      ENNReal.ofReal δ := by
  have hH : ∀ m, Measurable (fun x : R × Prefix m => (L m x + U m x)/2) :=
    fun m => ((hL m).add (hU m)).div_const 2
  have ha := online_prefix_accuracy μ A _ hH t (interval_midpoint_accuracy μ A L U t hc) q hq n
  let s := {x : R × Prefix n | |(L n x + U n x)/2 - signMean μ q.val| ≤ t n}
  have hs : MeasurableSet s := measurableSet_le (((hH n).sub measurable_const).abs) measurable_const
  have hcompl : {x : R × Prefix n | t n < |(L n x + U n x)/2 - signMean μ q.val|} = sᶜ := by
    ext x; simp [s, not_le]
  have hreal : (observablePrefixLaw μ A q n).real sᶜ ≤ δ := by
    rw [probReal_compl_eq_one_sub hs]; linarith
  rw [hcompl, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- If `n ≥ 2` and `log log n ≤ (10^{10} - 1) log(1/δ)`, the selection functional
at `n / Λ_n` is at most `10^5` times its value at `n / log(1/δ)`. When
`log log n ≥ 0` this is the square-root scaling in the budget ratio
`Λ_n / log(1/δ) ≤ 10^{10}`; at `n = 2`, `Λ_2 < log(1/δ)` and the functional
is antitone in the budget. -/
theorem inflation_selection {μ : Measure Gap} {ρ δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1/4)
    {n : ℕ} (hn : 2 ≤ n)
    (hlog : Real.log (Real.log (n : ℝ)) ≤ ((10 : ℝ) ^ 10 - 1) * Real.log (1/δ)) :
    ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ)/budgetInflation δ n) ≤
      ENNReal.ofReal ((10 : ℝ) ^ 5) *
        ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ)/Real.log (1/δ)) := by
  have hℓ : 0 < Real.log (1/δ) := ThresholdHC.Confidence.confidence_log_pos hδ hδ4
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hlogn : (1/2 : ℝ) < Real.log (n : ℝ) :=
    lt_of_lt_of_le (by linarith) (Real.log_le_log (by norm_num) h2)
  have hll : -1 < Real.log (Real.log (n : ℝ)) := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 1/2) hlogn
    have hh : Real.log (1/2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    linarith
  have hℓ1 : 1 < Real.log (1/δ) := by
    have h4 : Real.log 4 ≤ Real.log (1/δ) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ]; linarith)
    have h44 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hΛpos : 0 < budgetInflation δ n := by unfold budgetInflation; linarith
  have hΛ' : budgetInflation δ n ≤ (10 : ℝ) ^ 10 * Real.log (1/δ) := by
    unfold budgetInflation; linarith
  have hb : 0 < (n : ℝ)/budgetInflation δ n := div_pos hn0 hΛpos
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((10 : ℝ) ^ 5) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  by_cases hΛ : Real.log (1/δ) ≤ budgetInflation δ n
  · have hbB : (n : ℝ)/budgetInflation δ n ≤ (n : ℝ)/Real.log (1/δ) :=
      div_le_div_of_nonneg_left hn0.le hℓ hΛ
    have hscale := ThresholdHC.HardBudget.selection_budget_scale μ ρ hb hbB
    have hratio : ((n : ℝ)/Real.log (1/δ)) / ((n : ℝ)/budgetInflation δ n) =
        budgetInflation δ n / Real.log (1/δ) := by
      field_simp
    have hsqrt : Real.sqrt (((n : ℝ)/Real.log (1/δ)) / ((n : ℝ)/budgetInflation δ n)) ≤
        (10 : ℝ) ^ 5 := by
      rw [hratio, Real.sqrt_le_left (by positivity), div_le_iff₀ hℓ]
      nlinarith [hΛ']
    exact hscale.trans (by gcongr)
  · have hBb : (n : ℝ)/Real.log (1/δ) ≤ (n : ℝ)/budgetInflation δ n :=
      div_le_div_of_nonneg_left hn0.le hΛpos (le_of_not_ge hΛ)
    calc ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ)/budgetInflation δ n)
        ≤ ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ)/Real.log (1/δ)) :=
          ThresholdHC.Anytime.selection_antitone μ ρ (div_pos hn0 hℓ) hBb
      _ = 1 * ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ)/Real.log (1/δ)) := (one_mul _).symm
      _ ≤ _ := by gcongr

end ThresholdHC.StoppedTimeUniform
