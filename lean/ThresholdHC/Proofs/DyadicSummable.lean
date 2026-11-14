import ThresholdHC.Proofs.Classifier

/-! Convergence of the two dyadic series of the frozen targets H3 and H4.

`Targets.dyadic_sum_v1` and `Targets.dyadic_sum_v2` bound `∑'` sums. In Mathlib
the sum of a series that does not converge is `0`, so those targets alone do
not say that the series converge. The specification file is frozen; these
theorems add the convergence, from the same partial-sum bounds, and restate
each bound as a `HasSum` statement. -/

noncomputable section

namespace ThresholdHC.Proofs

theorem dyadic_partial_v1 {b : ℝ} (hb : 0 < b) (m : ℕ) :
    ∑ k ∈ Finset.range m, (2:ℝ)^k * Real.exp (-(b*2^k)) ≤ 2 / b := by
  have hpartial : ∀ m : ℕ,
      b * (∑ k ∈ Finset.range m, (2:ℝ)^k * Real.exp (-(b*2^k)))
      ≤ 2 * (Real.exp (-(b/2)) - Real.exp (-(b*2^m/2))) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hpow : b * (2:ℝ)^(m+1) / 2 = b * 2^m := by rw [pow_succ]; ring
      rw [hpow]
      have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (b * (2:ℝ)^m / 2))
        (Real.exp_pos (-(b * (2:ℝ)^m))).le
      have heq : Real.exp (b * (2:ℝ)^m / 2) * Real.exp (-(b * (2:ℝ)^m)) =
          Real.exp (-(b * (2:ℝ)^m / 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [heq] at h
      have hb2 : 0 ≤ b * (2:ℝ)^m := by positivity
      nlinarith only [ih, h, hb2, Real.exp_pos (-(b * (2:ℝ)^m))]
  apply (le_div_iff₀ hb).2
  have hs := hpartial m
  have hstart : Real.exp (-(b/2)) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (show -(b/2) ≤ 0 by linarith)
  have hend := (Real.exp_pos (-(b*(2:ℝ)^m/2))).le
  nlinarith only [hs, hstart, hend]

/-- H3 converges: `Σ_k 2^k e^{-b 2^k}` is summable, with sum at most `2/b`. -/
theorem dyadic_hasSum_v1 {b : ℝ} (hb : 0 < b) :
    ∃ s, HasSum (fun k : ℕ => (2:ℝ)^k * Real.exp (-(b*2^k))) s ∧ s ≤ 2 / b :=
  ⟨_, (summable_of_sum_range_le (fun k => by positivity) (dyadic_partial_v1 hb)).hasSum,
    dyadic_sum_v1 b hb⟩

/-- Each term of H4 is at most `2/b` times a term of H3 at `b/2`, since
`x e^{-x} ≤ 1` for `x = b 2^k / 2`. -/
theorem dyadic_term_v2 {b : ℝ} (hb : 0 < b) (k : ℕ) :
    ((2:ℝ)^k)^2 * Real.exp (-(b*2^k)) ≤ (2 / b) * ((2:ℝ)^k * Real.exp (-((b/2)*2^k))) := by
  set x := (b/2) * (2:ℝ)^k with hxdef
  have hp : (0:ℝ) < 2^k := by positivity
  have hx0 : 0 ≤ x := by positivity
  have he := Real.exp_pos (-x)
  have hkey : x * Real.exp (-x) ≤ 1 := by
    have h1 := Real.add_one_le_exp x
    have hinv : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have hsplit : Real.exp (-(b*2^k)) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add, hxdef]
    congr 1
    ring
  have h2k : (2:ℝ)^k = (2 / b) * x := by
    rw [hxdef]
    field_simp
  rw [hsplit]
  calc ((2:ℝ)^k)^2 * (Real.exp (-x) * Real.exp (-x))
      = (2 / b) * ((2:ℝ)^k * Real.exp (-x)) * (x * Real.exp (-x)) := by
        rw [sq]
        nth_rewrite 2 [h2k]
        ring
    _ ≤ (2 / b) * ((2:ℝ)^k * Real.exp (-x)) * 1 :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = _ := by ring

theorem dyadic_partial_v2 {b : ℝ} (hb : 0 < b) (m : ℕ) :
    ∑ k ∈ Finset.range m, ((2:ℝ)^k)^2 * Real.exp (-(b*2^k)) ≤ 8 / b^2 := by
  calc ∑ k ∈ Finset.range m, ((2:ℝ)^k)^2 * Real.exp (-(b*2^k))
      ≤ ∑ k ∈ Finset.range m, (2 / b) * ((2:ℝ)^k * Real.exp (-((b/2)*2^k))) :=
        Finset.sum_le_sum fun k _ => dyadic_term_v2 hb k
    _ = (2 / b) * ∑ k ∈ Finset.range m, (2:ℝ)^k * Real.exp (-((b/2)*2^k)) := by
        rw [Finset.mul_sum]
    _ ≤ (2 / b) * (2 / (b/2)) :=
        mul_le_mul_of_nonneg_left (dyadic_partial_v1 (by linarith) m) (by positivity)
    _ = 8 / b^2 := by field_simp; ring

/-- H4 converges: `Σ_k 4^k e^{-b 2^k}` is summable, with sum at most `8/(3b²)`. -/
theorem dyadic_hasSum_v2 {b : ℝ} (hb : 0 < b) :
    ∃ s, HasSum (fun k : ℕ => ((2:ℝ)^k)^2 * Real.exp (-(b*2^k))) s ∧ s ≤ 8 / (3 * b^2) :=
  ⟨_, (summable_of_sum_range_le (fun k => by positivity) (dyadic_partial_v2 hb)).hasSum,
    dyadic_sum_v2 b hb⟩

end ThresholdHC.Proofs
