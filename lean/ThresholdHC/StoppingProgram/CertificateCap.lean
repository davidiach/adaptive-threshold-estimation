import ThresholdHC.StoppingProgram.Specification

/-! The prescribed finite cap makes the truncation penalty no greater than
the universal Bernoulli-label risk floor. -/

noncomputable section
namespace ThresholdHC.StoppingProgram

theorem certificateCap_bounds (ρ B : ℝ) :
    64*B ≤ (certificateCap ρ B : ℝ) ∧
      64*(ρ*B^2) ≤ (certificateCap ρ B : ℝ) := by
  have h : 64*max B (ρ*B^2) ≤ (certificateCap ρ B : ℝ) := Nat.le_ceil _
  constructor
  · exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)).trans h
  · exact (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)).trans h

theorem certificateCap_pos (ρ B : ℝ) (hB : 0 < B) : 0 < certificateCap ρ B := by
  have h := (certificateCap_bounds ρ B).1
  have hp : (0:ℝ) < (certificateCap ρ B : ℝ) := lt_of_lt_of_le (by positivity) h
  exact_mod_cast hp

theorem certificateCap_error (ρ B : ℝ) (hρ : 0 < ρ) (hB : 0 < B) :
    ρ/2*Real.sqrt (B/((certificateCap ρ B:ℝ)+1)) ≤
      (1/16:ℝ)*min ρ (Real.sqrt (ρ/B)) := by
  let D := (certificateCap ρ B:ℝ)+1
  have hD : 0 < D := by dsimp only [D]; positivity
  have hBD : 64*B ≤ D := by have h := (certificateCap_bounds ρ B).1; dsimp only [D]; linarith
  have hρBD : 64*(ρ*B^2) ≤ D := by have h := (certificateCap_bounds ρ B).2; dsimp only [D]; linarith
  have hf1 : B/D ≤ (1/8:ℝ)^2 := (div_le_iff₀ hD).mpr (by nlinarith)
  have hs1 : Real.sqrt (B/D) ≤ 1/8 := Real.sqrt_le_iff.mpr ⟨by norm_num,hf1⟩
  have hfirst : ρ/2*Real.sqrt (B/D) ≤ ρ/16 := by nlinarith [mul_le_mul_of_nonneg_left hs1 hρ.le]
  have hden : 0 < 64*ρ*B := by positivity
  have hf2 : B/D ≤ 1/(64*ρ*B) := (div_le_div_iff₀ hD hden).mpr (by nlinarith)
  have hmul := mul_le_mul_of_nonneg_left hf2 (sq_nonneg (ρ/2))
  have he : (ρ/2)^2*(1/(64*ρ*B)) = (ρ/B)/16^2 := by field_simp; ring
  rw [he] at hmul
  have hs2 : (ρ/2*Real.sqrt (B/D))^2 ≤ (Real.sqrt (ρ/B)/16)^2 := by
    simp only [mul_pow,div_pow,Real.sq_sqrt (div_nonneg hB.le hD.le),Real.sq_sqrt (div_nonneg hρ.le hB.le)]
    simpa only [div_pow] using hmul
  have hsecond : ρ/2*Real.sqrt (B/D) ≤ Real.sqrt (ρ/B)/16 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hs2
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/16)]
  apply le_min
  · simpa only [D,div_eq_mul_inv,one_mul,mul_comm] using hfirst
  · simpa only [D,div_eq_mul_inv,one_mul,mul_comm] using hsecond

end ThresholdHC.StoppingProgram
