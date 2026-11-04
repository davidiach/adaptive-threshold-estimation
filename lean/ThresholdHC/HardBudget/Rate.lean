import ThresholdHC.HardBudget.Schedule

noncomputable section
open scoped ENNReal
namespace ThresholdHC.HardBudget

private theorem scaled_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (f : ℝ → ℝ)
    (hfx : 0 ≤ f x) (h : f x ≤ Real.sqrt (y/x)*f y) :
    (f x)^2 ≤ (y/x)*(f y)^2 := by
  have h2 := pow_le_pow_left₀ hfx h 2
  rwa [mul_pow,Real.sq_sqrt (div_nonneg hy hx)] at h2

/-- Accumulated stage losses, with the exact reservation schedule and
midpoint initialization. The conclusion is uniform over the base rate. -/
theorem fallback_rate {B C M θ : ℝ} (hb : 4 ≤ B) (hC : 1/2 ≤ C)
    (hθ : 0 ≤ θ ∧ θ ≤ M) (f : ℝ → ℝ) (hf : ∀ b, 1/2 ≤ b → 0 ≤ f b)
    (hM : f (1/2) = M) (hs : ∀ b b', 1/2 ≤ b → b ≤ b' → f b ≤ Real.sqrt (b'/b)*f b')
    (D : ℕ → ℝ≥0∞) (hinit : D 0 ≤ ENNReal.ofReal ((M/2-θ)^2))
    (hstep : ∀ j, D (j+1) ≤ ENNReal.ofReal (C^2*(f (stageAllowance j))^2)+(1/4)*D j) :
    D (stageCount B) ≤ ENNReal.ofReal (32*C^2*(f B)^2) := by
  have hB : 0 ≤ B := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hM0 : 0 ≤ M := hθ.1.trans hθ.2
  have hhalf : M^2 ≤ (B/(1/2))*(f B)^2 := by
    rw [← hM]
    exact scaled_sq (by norm_num) hB f (hf _ le_rfl) (hs _ _ le_rfl (by linarith))
  let a (j : ℕ) : ℝ := (2:ℝ)^j
  have ha (j : ℕ) : 0 < a j := pow_pos (by norm_num) _
  have haj (j : ℕ) : (stageAllowance j:ℝ) = a j := by simp [stageAllowance,a]
  let V (j : ℕ) := 4*C^2*(B/a j)*(f B)^2
  have hV (j) : 0 ≤ V j := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (div_nonneg hB (ha j).le)) (sq_nonneg _)
  have hi : ∀ j ≤ stageCount B, D j ≤ ENNReal.ofReal (V j) := by
    intro j; induction j with
    | zero =>
      intro _
      apply hinit.trans; apply ENNReal.ofReal_le_ofReal
      have hmid : (M/2-θ)^2 ≤ (M/2)^2 := by nlinarith [mul_nonneg hθ.1 (sub_nonneg.mpr hθ.2)]
      have hcs : (1/2:ℝ)^2 ≤ C^2 := pow_le_pow_left₀ (by norm_num) hC 2
      dsimp [V,a]
      calc (M/2-θ)^2 ≤ (M/2)^2 := hmid
           _ ≤ C^2*M^2 := by nlinarith only [mul_le_mul_of_nonneg_right hcs (sq_nonneg M)]
           _ ≤ C^2*((B/(1/2))*(f B)^2) := mul_le_mul_of_nonneg_left hhalf (sq_nonneg _)
           _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (sq_nonneg C) hB) (sq_nonneg (f B))]
    | succ j ih =>
      intro hj
      have hpre := ih (by omega)
      have hp := (Nat.le_floor_iff hB).mp ((paid_strict.monotone hj).trans (paid_fits B))
      have hsmall : a j ≤ B := by
        have hnum : stageAllowance j ≤ paid (j+1) := by dsimp [paid,stageCap]; omega
        rw [← haj]; exact (Nat.cast_le.mpr hnum).trans hp
      have hge : 1/2 ≤ a j := by have h := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j); dsimp [a]; linarith
      have hf2 := scaled_sq (ha j).le hB f (hf _ hge) (hs _ _ hge hsmall)
      apply (hstep j).trans
      refine (add_le_add le_rfl (mul_le_mul_right hpre _)).trans ?_
      rw [← show ENNReal.ofReal (1/4:ℝ) = (1/4:ℝ≥0∞) by rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<4)]; norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/4),
        ← ENNReal.ofReal_add (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_nonneg (by norm_num) (hV j))]
      apply ENNReal.ofReal_le_ofReal
      rw [haj]
      have hv : (1/4)*V j = C^2*(B/a j)*(f B)^2 := by dsimp [V]; ring
      have hv' : V (j+1) = 2*(C^2*(B/a j)*(f B)^2) := by dsimp [V,a]; rw [pow_succ]; ring
      rw [hv,hv']; nlinarith only [mul_le_mul_of_nonneg_left hf2 (sq_nonneg C)]
  apply (hi _ le_rfl).trans; apply ENNReal.ofReal_le_ofReal
  let k := stageCount B
  have hnext : B < paid (k+1) := (Nat.floor_lt hB).mp (next_exceeds B)
  have hpf : (paid (k+1):ℝ)+4 = 4*(2:ℝ)^(k+1) := by exact_mod_cast paid_formula (k+1)
  rw [pow_succ] at hpf
  have hfac : B/a k ≤ 8 := (div_le_iff₀ (ha k)).2 (by dsimp [a]; linarith)
  change 4*C^2*(B/a k)*(f B)^2 ≤ _
  nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac (sq_nonneg C)) (sq_nonneg (f B))]

end ThresholdHC.HardBudget
