import Mathlib

noncomputable section


namespace ThresholdHC.CriticalEntropy

/-- A universal small separation gives the saturated square-root rate. -/
theorem critical_rate_separation (C : ℝ) (hC : 0 < C) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ρ K B : ℝ), 0 < ρ → 0 < K → 0 < B →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ/96 ∧ C*δ^2*B ≤ K/4 ∧
        c*min ρ (Real.sqrt (K/B)) ≤ δ/8 := by
  let κ := min (1/96 : ℝ) (1/(2*Real.sqrt C))
  have hs : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC
  have hκ : 0 < κ := lt_min (by norm_num) (by positivity)
  refine ⟨κ/8,by positivity,?_⟩
  intro ρ K B hρ hK hB
  let m := min ρ (Real.sqrt (K/B))
  have hm : 0 < m := lt_min hρ (Real.sqrt_pos.mpr (div_pos hK hB))
  refine ⟨κ*m,mul_pos hκ hm,?_,?_,?_⟩
  · calc
      κ*m ≤ κ*ρ := mul_le_mul_of_nonneg_left (min_le_left _ _) hκ.le
      _ ≤ (1/96)*ρ := mul_le_mul_of_nonneg_right (min_le_left _ _) hρ.le
      _ = ρ/96 := by ring
  · have hκs : κ*Real.sqrt C ≤ 1/2 := by
      calc
        κ*Real.sqrt C ≤ (1/(2*Real.sqrt C))*Real.sqrt C :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hs.le
        _ = 1/2 := by field_simp
    have hκsq : C*κ^2 ≤ 1/4 := by
      calc
        C*κ^2 = (κ*Real.sqrt C)^2 := by rw [mul_pow,Real.sq_sqrt hC.le]; ring
        _ ≤ (1/2 : ℝ)^2 := (sq_le_sq₀ (mul_nonneg hκ.le hs.le) (by norm_num)).2 hκs
        _ = 1/4 := by norm_num
    have hmsq : m^2 ≤ K/B := by
      calc
        m^2 ≤ (Real.sqrt (K/B))^2 :=
          (sq_le_sq₀ hm.le (Real.sqrt_nonneg _)).2 (min_le_right _ _)
        _ = K/B := Real.sq_sqrt (div_nonneg hK.le hB.le)
    have hmB : m^2*B ≤ K := (le_div_iff₀ hB).mp hmsq
    calc
      C*(κ*m)^2*B = (C*κ^2)*(m^2*B) := by ring
      _ ≤ (1/4)*K := mul_le_mul hκsq hmB (mul_nonneg (sq_nonneg _) hB.le) (by norm_num)
      _ = K/4 := by ring
  · dsimp [m]
    ring_nf
    exact le_rfl

end ThresholdHC.CriticalEntropy
