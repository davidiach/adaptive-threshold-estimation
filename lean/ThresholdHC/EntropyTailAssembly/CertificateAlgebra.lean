import ThresholdHC.EntropyTailAssembly.UnresolvedWork

/-! Finite multilevel square-root certificate estimates. -/

noncomputable section
open MeasureTheory Set Real
open scoped BigOperators

namespace ThresholdHC.EntropyTailAssembly

theorem sqrt_add_subadditive {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    sqrt (a+b) ≤ sqrt a+sqrt b := by
  apply sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [sq_sqrt ha, sq_sqrt hb, mul_nonneg (sqrt_nonneg a) (sqrt_nonneg b)]

theorem quarter_linear_sum (n : ℕ) :
    (∑ l ∈ Finset.range n, (l+1:ℝ)*(1/4:ℝ)^(l+1)) ≤ 4/9 := by
  have hg := hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1/4:ℝ) < 1)
  have hn := hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1/4:ℝ)‖ < 1)
  have h : HasSum (fun l : ℕ => (l+1:ℝ)*(1/4:ℝ)^(l+1)) (4/9) := by
    convert (hg.add hn).mul_left (1/4:ℝ) using 1
    · ext l; rw [pow_succ]; ring
    · norm_num
  exact sum_le_hasSum _ (fun _ _ => by positivity) h

theorem quarter_tail_sum (n : ℕ) : (∑ l ∈ Finset.range n, (1/4:ℝ)^(l+1)) ≤ 1/3 := by
  have h := mul_le_mul_of_nonneg_left (quarter_geometric_sum n) (by norm_num : (0:ℝ) ≤ 1/4)
  simpa only [Finset.mul_sum, ← pow_succ'] using h.trans_eq (by norm_num)

theorem level_work_root {ρ Γ H z M O : ℝ} (hρ : 0 < ρ) (hΓ : 0 ≤ Γ)
    (hH : 0 ≤ H) (hz : 0 ≤ z) (hM : 0 ≤ M) (hO : 0 ≤ O) (l : ℕ) :
    sqrt (levelAccuracy ρ l*(128*(l+1)*Γ+6*H^2/ρ+2*O+2*z*M)) ≤
      12*sqrt (ρ*Γ)*(l+1)*(1/4:ℝ)^(l+1) + 3*H*(1/4:ℝ)^(l+1) +
      (3/2)*sqrt (levelAccuracy ρ l*O)+(3/2)*sqrt (z*levelAccuracy ρ l*M) := by
  let δ := levelAccuracy ρ l
  have hδ : 0 < δ := levelAccuracy_pos hρ l
  have hs : sqrt (δ*(128*(l+1)*Γ)) ≤ 12*sqrt (ρ*Γ)*(l+1)*(1/4:ℝ)^(l+1) := by
    have he : sqrt (ρ*Γ)*(1/4:ℝ)^(l+1) = sqrt (δ*Γ) := by
      rw [sqrt_mul hρ.le, sqrt_mul hδ.le, sqrt_levelAccuracy hρ.le]
      ring
    have he' : 12*sqrt (ρ*Γ)*(l+1)*(1/4:ℝ)^(l+1) = 12*(l+1)*sqrt (δ*Γ) := by
      calc
        _ = 12*(l+1)*(sqrt (ρ*Γ)*(1/4:ℝ)^(l+1)) := by ring
        _ = _ := by rw [he]
    rw [he']
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have heq : (12*(l+1)*sqrt (δ*Γ))^2 = 144*(l+1)^2*(δ*Γ) := by
      rw [mul_pow, sq_sqrt (mul_nonneg hδ.le hΓ)]
      ring
    rw [heq]
    have hp : (128:ℝ)*(l+1) ≤ 144*(l+1)^2 := by nlinarith [sq_nonneg (l:ℝ), Nat.cast_nonneg (α := ℝ) l]
    nlinarith [mul_le_mul_of_nonneg_right hp (mul_nonneg hδ.le hΓ)]
  have hh : sqrt (δ*(6*H^2/ρ)) ≤ 3*H*(1/4:ℝ)^(l+1) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have he : δ = ρ*((1/4:ℝ)^(l+1))^2 := by
      have h := sq_sqrt hδ.le
      rw [sqrt_levelAccuracy hρ.le, mul_pow, sq_sqrt hρ.le] at h
      exact h.symm
    rw [he]
    field_simp
    nlinarith [sq_nonneg (H*(1/4:ℝ)^(l+1))]
  have ho : sqrt (δ*(2*O)) ≤ (3/2)*sqrt (δ*O) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_sqrt (mul_nonneg hδ.le hO), mul_nonneg hδ.le hO]
  have hz' : sqrt (δ*(2*z*M)) ≤ (3/2)*sqrt (z*δ*M) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_sqrt (mul_nonneg (mul_nonneg hz hδ.le) hM), mul_nonneg (mul_nonneg hz hδ.le) hM]
  have ht := sqrt_add_subadditive
    (show 0 ≤ δ*(128*(l+1)*Γ)+δ*(6*H^2/ρ)+δ*(2*O) by positivity)
    (show 0 ≤ δ*(2*z*M) by positivity)
  have ht2 := sqrt_add_subadditive
    (show 0 ≤ δ*(128*(l+1)*Γ)+δ*(6*H^2/ρ) by positivity) (show 0 ≤ δ*(2*O) by positivity)
  have ht3 := sqrt_add_subadditive
    (show 0 ≤ δ*(128*(l+1)*Γ) by positivity) (show 0 ≤ δ*(6*H^2/ρ) by positivity)
  change sqrt (δ*_) ≤ _
  rw [mul_add, mul_add, mul_add]
  linarith

def adjacentCost (C : ℕ → ℝ) (l : ℕ) : ℝ := if l = 0 then C l else C l+C (l-1)

theorem adjacent_root_level {ρ : ℝ} (hρ : 0 < ρ) (C : ℕ → ℝ) (hC : ∀ l, 0 ≤ C l) (l : ℕ) :
    sqrt (17*levelAccuracy ρ l*adjacentCost C l) ≤ sqrt 17 *
      (sqrt (levelAccuracy ρ l*C l)+(if l = 0 then 0 else sqrt (levelAccuracy ρ (l-1)*C (l-1))/4)) := by
  cases l with
  | zero => simp only [adjacentCost, ite_true, add_zero]; rw [mul_assoc, sqrt_mul (by norm_num)]
  | succ l =>
    simp only [adjacentCost, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    have he : sqrt (levelAccuracy ρ (l+1)*C l) = sqrt (levelAccuracy ρ l*C l)/4 := by
      rw [levelAccuracy_succ]
      have he' : levelAccuracy ρ l/16*C l = (levelAccuracy ρ l*C l)/16 := by ring
      rw [he', sqrt_div (mul_nonneg (levelAccuracy_pos hρ l).le (hC l))]
      norm_num
    rw [mul_assoc, sqrt_mul (by norm_num : (0:ℝ) ≤ 17), mul_add]
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg 17)
    exact (sqrt_add_subadditive (by positivity [hC (l+1), levelAccuracy_pos hρ (l+1)])
      (by positivity [hC l, levelAccuracy_pos hρ (l+1)])).trans_eq (by rw [he])

theorem adjacent_root_sum {ρ : ℝ} (hρ : 0 < ρ) (C : ℕ → ℝ) (hC : ∀ l, 0 ≤ C l) (J : ℕ) :
    (∑ l ∈ Finset.range (J+1), sqrt (17*levelAccuracy ρ l*adjacentCost C l)) ≤
      (21/4:ℝ)*∑ l ∈ Finset.range (J+1), sqrt (levelAccuracy ρ l*C l) := by
  let f := fun l => sqrt (levelAccuracy ρ l*C l)
  have h := Finset.sum_le_sum (s := Finset.range (J+1)) (fun l _ => adjacent_root_level hρ C hC l)
  change _ ≤ ∑ l ∈ Finset.range (J+1), sqrt 17*(f l+(if l = 0 then 0 else f (l-1)/4)) at h
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at h
  have he : (∑ l ∈ Finset.range (J+1), (if l = 0 then 0 else f (l-1)/4)) =
      (∑ l ∈ Finset.range J, f l)/4 := by
    rw [Finset.sum_range_succ']
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, Nat.add_sub_cancel,
      ite_true, add_zero, Finset.sum_div]
  rw [he] at h
  have hs : (∑ l ∈ Finset.range J, f l) ≤ ∑ l ∈ Finset.range (J+1), f l := by
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (sqrt_nonneg _)
  have hn : 0 ≤ ∑ l ∈ Finset.range (J+1), f l := Finset.sum_nonneg (fun _ _ => sqrt_nonneg _)
  have hr : sqrt (17:ℝ) ≤ 21/5 := by apply sqrt_le_iff.mpr; norm_num
  have h1 := mul_le_mul_of_nonneg_left hs (sqrt_nonneg 17)
  have h2 := mul_le_mul_of_nonneg_right hr hn
  change _ ≤ (21/4:ℝ)*∑ l ∈ Finset.range (J+1), f l
  nlinarith only [h, h1, h2]

end ThresholdHC.EntropyTailAssembly
