import ThresholdHC.BiasAudit.Specification
import ThresholdHC.BiasAudit.Measure

/-! The smaller-threshold error bound of `proposals/constants/BIAS_AUDIT.md:6-41`. For
`k1 ≥ 0` and `k2 ≥ 1` the frozen classifier with threshold `thrK k1 k2` keeps the v4
envelope. The argument is the coefficient-generic form of `Tier2.Model`
(`Proofs/Tier2/ClassifierModel.lean`): a union bound over the potential early stops and
the cap decision, Hoeffding tails, `(d+t)² ≥ d² + t²`, `(n/N)^{2k2} ≤ (n/N)²`, and the
dyadic sum `Σ n² exp(-b n) ≤ 8/(3b²)`. -/
noncomputable section
namespace ThresholdHC.BiasAudit
open MeasureTheory ProbabilityTheory Real
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Uniform713

/-- The frozen threshold at dyadic prefixes in terms of `cap`. -/
theorem finiteBoundary_eq_cap (k1 k2 : ℝ) (j L : ℕ) :
    finiteBoundary k1 k2 j L = Real.sqrt ((k1 + k2 * Real.log (cap L / cap j)) / cap j) := by
  unfold finiteBoundary thrK cap
  simp only [Nat.cast_pow, Nat.cast_ofNat]

theorem log_cap_ratio_nonneg {j L : ℕ} (hjL : j ≤ L) : 0 ≤ Real.log (cap L / cap j) :=
  Real.log_nonneg ((one_le_div (cap_pos j)).2 (cap_mono hjL))

/-- The squared threshold: `t(n,N)² = (k1 + k2 log(N/n))/n`. -/
theorem finiteBoundary_sq {k1 k2 : ℝ} (hk1 : 0 ≤ k1) (hk2 : 0 ≤ k2) {j L : ℕ}
    (hjL : j ≤ L) :
    (finiteBoundary k1 k2 j L) ^ 2 = (k1 + k2 * Real.log (cap L / cap j)) / cap j := by
  rw [finiteBoundary_eq_cap]
  apply Real.sq_sqrt
  have := log_cap_ratio_nonneg hjL
  have := cap_pos j
  positivity

/-- The union-bound sum: the wrong cap decision and every wrong early stop. -/
def errorUnionBoundK (k1 k2 : ℝ) (L : ℕ) (d : ℝ) : ℝ :=
  Real.exp (-2 * cap L * d ^ 2) +
    ∑ k ∈ Finset.range L, Real.exp (-2 * cap k * (d + finiteBoundary k1 k2 k L) ^ 2)

theorem error_positive_union_gen {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : ℕ → Ω → ℝ} (k1 k2 : ℝ) (L : ℕ) {d : ℝ} (hd : 0 < d)
    (ht : HasMeanTails μ m (1/2+d)) :
    μ.real {ω | firstDecision (finiteBoundary k1 k2) (fun k => m k ω) L ≠ 1} ≤
      errorUnionBoundK k1 k2 L d := by
  have hsub : {ω | firstDecision (finiteBoundary k1 k2) (fun k => m k ω) L ≠ 1} ⊆
      {ω | d ≤ (1/2+d)-m L ω} ∪
        ⋃ k ∈ Finset.range L,
          {ω | d+finiteBoundary k1 k2 k L ≤ (1/2+d)-m k ω} := by
    intro ω hω
    rcases wrong_positive_stop (finiteBoundary k1 k2)
      (fun k => m k ω) L d hω with ⟨_, h⟩ | ⟨hs, h⟩
    · exact Or.inl h
    · right
      exact Set.mem_iUnion.2 ⟨_, Set.mem_iUnion.2 ⟨Finset.mem_range.2 hs, h⟩⟩
  calc
    _ ≤ μ.real ({ω | d ≤ (1/2+d)-m L ω} ∪
        ⋃ k ∈ Finset.range L,
          {ω | d+finiteBoundary k1 k2 k L ≤ (1/2+d)-m k ω}) := measureReal_mono hsub
    _ ≤ μ.real {ω | d ≤ (1/2+d)-m L ω} +
        ∑ k ∈ Finset.range L,
          μ.real {ω | d+finiteBoundary k1 k2 k L ≤ (1/2+d)-m k ω} :=
      (measureReal_union_le _ _).trans
        (add_le_add_right (measureReal_biUnion_finset_le _ _) _)
    _ ≤ errorUnionBoundK k1 k2 L d := by
      unfold errorUnionBoundK
      apply add_le_add (ht.lower L d hd.le)
      apply Finset.sum_le_sum
      intro k _
      exact ht.lower k _ (add_nonneg hd.le (finiteBoundary_nonneg _ _ _ _))

theorem error_negative_union_gen {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : ℕ → Ω → ℝ} (k1 k2 : ℝ) (L : ℕ) {d : ℝ} (hd : 0 < d)
    (ht : HasMeanTails μ m (1/2-d)) :
    μ.real {ω | firstDecision (finiteBoundary k1 k2) (fun k => m k ω) L ≠ 0} ≤
      errorUnionBoundK k1 k2 L d := by
  have hsub : {ω | firstDecision (finiteBoundary k1 k2) (fun k => m k ω) L ≠ 0} ⊆
      {ω | d ≤ m L ω-(1/2-d)} ∪
        ⋃ k ∈ Finset.range L,
          {ω | d+finiteBoundary k1 k2 k L ≤ m k ω-(1/2-d)} := by
    intro ω hω
    rcases wrong_negative_stop (finiteBoundary k1 k2)
      (fun k => m k ω) L d hω with ⟨_, h⟩ | ⟨hs, h⟩
    · exact Or.inl h
    · right
      exact Set.mem_iUnion.2 ⟨_, Set.mem_iUnion.2 ⟨Finset.mem_range.2 hs, h⟩⟩
  calc
    _ ≤ μ.real ({ω | d ≤ m L ω-(1/2-d)} ∪
        ⋃ k ∈ Finset.range L,
          {ω | d+finiteBoundary k1 k2 k L ≤ m k ω-(1/2-d)}) := measureReal_mono hsub
    _ ≤ μ.real {ω | d ≤ m L ω-(1/2-d)} +
        ∑ k ∈ Finset.range L,
          μ.real {ω | d+finiteBoundary k1 k2 k L ≤ m k ω-(1/2-d)} :=
      (measureReal_union_le _ _).trans
        (add_le_add_right (measureReal_biUnion_finset_le _ _) _)
    _ ≤ errorUnionBoundK k1 k2 L d := by
      unfold errorUnionBoundK
      apply add_le_add (ht.upper L d hd.le)
      apply Finset.sum_le_sum
      intro k _
      exact ht.upper k _ (add_nonneg hd.le (finiteBoundary_nonneg _ _ _ _))

/-- A wrong early stop at `n = 2^j < N = 2^L`:
`exp(-2n(d+t)²) ≤ exp(-2k1) N^{-2} n² exp(-2d²n)` when `k1 ≥ 0`, `k2 ≥ 1`. -/
theorem early_error_term_gen {k1 k2 : ℝ} (hk1 : 0 ≤ k1) (hk2 : 1 ≤ k2) {j L : ℕ}
    (hjL : j ≤ L) {d : ℝ} (hd : 0 ≤ d) :
    Real.exp (-2 * cap j * (d + finiteBoundary k1 k2 j L) ^ 2) ≤
      Real.exp (-2 * k1) / (cap L) ^ 2 * ((cap j) ^ 2 * Real.exp (-(2 * d ^ 2 * cap j))) := by
  have hn := cap_pos j
  have hN := cap_pos L
  have ht := finiteBoundary_nonneg k1 k2 j L
  have hs := finiteBoundary_sq hk1 (zero_le_one.trans hk2) hjL
  have hlog := log_cap_ratio_nonneg hjL
  have h1 : -2 * cap j * (d + finiteBoundary k1 k2 j L) ^ 2 ≤
      -2 * cap j * (d ^ 2 + (finiteBoundary k1 k2 j L) ^ 2) := by
    nlinarith [mul_nonneg hd ht, mul_nonneg hn.le (mul_nonneg hd ht)]
  have h2 : -2 * cap j * (d ^ 2 + (finiteBoundary k1 k2 j L) ^ 2) =
      -(2 * d ^ 2 * cap j) + -2 * k1 + -(2 * (k2 * Real.log (cap L / cap j))) := by
    rw [hs]
    field_simp
    ring
  have h3 : Real.log (cap L / cap j) ≤ k2 * Real.log (cap L / cap j) := by nlinarith
  have hexp : -2 * cap j * (d + finiteBoundary k1 k2 j L) ^ 2 ≤
      -(2 * d ^ 2 * cap j) + -2 * k1 + -(2 * Real.log (cap L / cap j)) := by
    linarith
  refine (Real.exp_le_exp.2 hexp).trans_eq ?_
  have he2 : Real.exp (2 * Real.log (cap L / cap j)) = (cap L / cap j) ^ 2 := by
    rw [show 2 * Real.log (cap L / cap j) =
        Real.log (cap L / cap j) + Real.log (cap L / cap j) by ring,
      Real.exp_add, Real.exp_log (div_pos hN hn)]
    ring
  rw [Real.exp_add, Real.exp_add, Real.exp_neg (2 * Real.log (cap L / cap j)), he2]
  field_simp

/-- The union-bound sum is at most `exp(-2x) + (2/3) exp(-2k1) x^{-2}`, `x = N d²`. -/
theorem errorUnionBoundK_le {k1 k2 : ℝ} (hk1 : 0 ≤ k1) (hk2 : 1 ≤ k2) (L : ℕ) {d : ℝ}
    (hd : 0 < d) :
    errorUnionBoundK k1 k2 L d ≤
      Real.exp (-2 * (cap L * d ^ 2)) + 2/3 * Real.exp (-2 * k1) * ((cap L * d ^ 2)⁻¹) ^ 2 := by
  have hN := cap_pos L
  have hsum : (∑ k ∈ Finset.range L,
      Real.exp (-2 * cap k * (d + finiteBoundary k1 k2 k L) ^ 2)) ≤
      Real.exp (-2 * k1) / (cap L) ^ 2 * (8 / (3 * (2 * d ^ 2) ^ 2)) := by
    calc
      _ ≤ ∑ k ∈ Finset.range L,
          Real.exp (-2 * k1) / (cap L) ^ 2 *
            ((cap k) ^ 2 * Real.exp (-(2 * d ^ 2 * cap k))) := by
        apply Finset.sum_le_sum
        intro k hk
        exact early_error_term_gen hk1 hk2 (Finset.mem_range.mp hk).le hd.le
      _ = Real.exp (-2 * k1) / (cap L) ^ 2 *
          ∑ k ∈ Finset.range L, (cap k) ^ 2 * Real.exp (-(2 * d ^ 2 * cap k)) := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (finite_dyadic_sum_v2 (by positivity) L)
        (by positivity)
  have heq1 : Real.exp (-2 * cap L * d ^ 2) = Real.exp (-2 * (cap L * d ^ 2)) := by
    congr 1
    ring
  have heq2 : Real.exp (-2 * k1) / (cap L) ^ 2 * (8 / (3 * (2 * d ^ 2) ^ 2)) =
      2/3 * Real.exp (-2 * k1) * ((cap L * d ^ 2)⁻¹) ^ 2 := by
    field_simp
    ring
  unfold errorUnionBoundK
  rw [heq1]
  linarith

theorem exp_neg_two_le_fifth : Real.exp (-2) ≤ (1/5 : ℝ) := by
  have he : 5 ≤ Real.exp (2 : ℝ) := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at h
    linarith
  rw [Real.exp_neg]
  apply (inv_le_iff_one_le_mul₀ (Real.exp_pos (2 : ℝ))).2
  linarith

/-- The explicit bound is at most `x^{-2}` for every `x > 0`; together with `e_N ≤ 1` this
gives the v4 envelope `min(1, x^{-2})`. -/
theorem explicit_le_envelope {k1 : ℝ} (hk1 : 0 ≤ k1) {x : ℝ} (hx : 0 < x) :
    Real.exp (-2 * x) + 2/3 * Real.exp (-2 * k1) * (x⁻¹) ^ 2 ≤ (x⁻¹) ^ 2 := by
  have he := Tier2.Model.exp_cap_error hx
  have h5 := exp_neg_two_le_fifth
  have hk : Real.exp (-2 * k1) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hy : 0 ≤ (x⁻¹) ^ 2 := sq_nonneg _
  have heq : Real.exp (-2) / x ^ 2 = Real.exp (-2) * (x⁻¹) ^ 2 := by
    rw [inv_pow, div_eq_mul_inv]
  rw [heq] at he
  have hm1 := mul_le_mul_of_nonneg_right h5 hy
  have hm2 := mul_le_mul_of_nonneg_right hk hy
  linarith

theorem smallerThreshold_error_measure (k1 k2 : ℝ) (L : ℕ)
    {d : ℝ} (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    (tapeMeasure (coinParameter d S hd hdmax)).real
      {ω | firstDecision (finiteBoundary k1 k2) (fun j => dyadicMean observations j ω) L ≠
        bit S} ≤ errorUnionBoundK k1 k2 L d := by
  have htail := tape_mean_tails (coinParameter d S hd hdmax)
  cases S
  · simpa [coinP, bit] using
      error_negative_union_gen k1 k2 L hd (by simpa [coinP, sub_eq_add_neg] using htail)
  · simpa [coinP, bit] using
      error_positive_union_gen k1 k2 L hd (by simpa [coinP, sub_eq_add_neg] using htail)

theorem smallerThresholdError : SmallerThresholdErrorStatement := by
  intro k1 k2 hk1 hk2 L d S hd hdmax
  rw [errProbK_eq_measure_gen k1 k2 L d S hd hdmax]
  have h1 := (smallerThreshold_error_measure k1 k2 L S hd hdmax).trans
    (errorUnionBoundK_le hk1 hk2 L hd)
  have hx : 0 < cap L * d ^ 2 := mul_pos (cap_pos L) (pow_pos hd 2)
  refine ⟨h1, le_min measureReal_le_one ?_⟩
  exact h1.trans (explicit_le_envelope hk1 hx)

end ThresholdHC.BiasAudit
