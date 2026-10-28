import ThresholdHC.CriticalUpper.ScreenMoments

/-! Rarity-dependent caps and asymmetric classifier thresholds. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713

def screenThreshold (J : ℕ) (ε : ℝ) : ℝ := 1+Real.log (((J : ℝ)+1)/ε)

theorem screenThreshold_ge_one (J : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ screenThreshold J ε := by
  have harg : 1 ≤ ((J : ℝ)+1)/ε := (one_le_div hε).mpr (by linarith [Nat.cast_nonneg (α := ℝ) J])
  have hlog := Real.log_nonneg harg
  dsimp [screenThreshold]
  linarith

theorem screenThreshold_error (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (J : ℝ)*Real.exp (-screenThreshold J ε) ≤ ε := by
  have hJ : 0 < (J : ℝ)+1 := by positivity
  have harg : 0 < ((J : ℝ)+1)/ε := div_pos hJ hε
  have hex : Real.exp (-screenThreshold J ε) = Real.exp (-1)*(ε/((J : ℝ)+1)) := by
    unfold screenThreshold
    rw [neg_add,Real.exp_add,Real.exp_neg (Real.log _),Real.exp_log harg]
    congr 1
    simp only [inv_div]
  rw [hex]
  have he := Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0)
  have hb := mul_le_mul_of_nonneg_right he (div_pos hε hJ).le
  have hJε : (J : ℝ)*(ε/((J : ℝ)+1)) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hJ).mpr
    nlinarith
  exact (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg J)).trans (by simpa using hJε)

theorem asymmetricThreshold_error (J : ℕ) (ε ρ : ℝ) (hε : 0 < ε) (hρ : 0 < ρ) :
    (J : ℝ)*Real.exp (-(screenThreshold J ε+Real.log (1/ρ))) ≤ ρ*ε := by
  have he : Real.exp (-(Real.log (1/ρ))) = ρ := by
    rw [Real.exp_neg,Real.exp_log (by positivity)]
    simp
  rw [neg_add,Real.exp_add,he]
  have h := mul_le_mul_of_nonneg_right (screenThreshold_error J ε hε) hρ.le
  nlinarith

theorem exists_rarity_level (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ m : ℕ, (2 : ℝ)^m ≤ 1/ρ ∧ 1/ρ < 2*(2 : ℝ)^m := by
  obtain ⟨m,hlo,hhi⟩ := exists_nat_pow_near (x := 1/ρ) (y := (2 : ℝ))
    ((one_le_div hρ).mpr hρ1) (by norm_num)
  refine ⟨m,hlo,?_⟩
  simpa only [pow_succ,mul_comm] using hhi

def rarityLevel (ρ : ℝ) : ℕ :=
  if h : 0 < ρ ∧ ρ ≤ 1 then Classical.choose (exists_rarity_level ρ h.1 h.2) else 0

theorem rarityLevel_bounds (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (2 : ℝ)^(rarityLevel ρ) ≤ 1/ρ ∧ 1/ρ < 2*(2 : ℝ)^(rarityLevel ρ) := by
  simp only [rarityLevel,dite_eq_left (show 0 < ρ ∧ ρ ≤ 1 from ⟨hρ,hρ1⟩)]
  exact Classical.choose_spec (exists_rarity_level ρ hρ hρ1)

def screenAccuracy (j : ℕ) : ℝ := ((16 : ℝ)^(j+1))⁻¹

def screenLevel (ρ : ℝ) (j : ℕ) : ℕ := rarityLevel ρ+4*(j+1)+5

def calibratedScreen (ρ : ℝ) (j : ℕ) : StoppedProcedure Unit ℝ :=
  screenProcedure (screenThreshold (screenLevel ρ j) (screenAccuracy j))
    (screenThreshold (screenLevel ρ j) (screenAccuracy j)+Real.log (1/ρ)) (screenLevel ρ j)

theorem screenAccuracy_pos (j : ℕ) : 0 < screenAccuracy j := by unfold screenAccuracy; positivity

theorem screenAccuracy_le_one (j : ℕ) : screenAccuracy j ≤ 1 := by
  apply inv_le_one_of_one_le₀
  exact one_le_pow₀ (by norm_num : 1 ≤ (16 : ℝ))

theorem screenLevel_cap (ρ : ℝ) (j : ℕ) :
    cap (screenLevel ρ j) = 32*(2 : ℝ)^(rarityLevel ρ)*(16 : ℝ)^(j+1) := by
  unfold cap screenLevel
  rw [pow_add,pow_add,pow_mul]
  norm_num
  ring

theorem screenLevel_gaussian (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j : ℕ) :
    8/cap (screenLevel ρ j) ≤ ρ*screenAccuracy j/2 := by
  have hm := (div_lt_iff₀ hρ).mp (rarityLevel_bounds ρ hρ hρ1).2
  have he : (ρ*screenAccuracy j/2)*cap (screenLevel ρ j) =
      16*ρ*(2 : ℝ)^(rarityLevel ρ) := by
    rw [screenLevel_cap]
    unfold screenAccuracy
    field_simp
    ring
  apply (div_le_iff₀ (cap_pos _)).mpr
  rw [he]
  nlinarith

theorem calibratedScreen_error (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j : ℕ)
    (q : ℝ → unitInterval) (hq : Measurable q)
    (hmass : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ) :
    screenPopulationError (screenThreshold (screenLevel ρ j) (screenAccuracy j))
      (screenThreshold (screenLevel ρ j) (screenAccuracy j)+Real.log (1/ρ)) (screenLevel ρ j) q ≤
    3*ρ*screenAccuracy j := by
  have hA := screenThreshold_ge_one (screenLevel ρ j) (screenAccuracy j)
    (screenAccuracy_pos j) (screenAccuracy_le_one j)
  have hr := Real.log_nonneg ((one_le_div hρ).mpr hρ1)
  have hb := screen_population_error_le _ _ (by linarith : 0 ≤ screenThreshold (screenLevel ρ j) (screenAccuracy j))
    (by linarith : 0 ≤ screenThreshold (screenLevel ρ j) (screenAccuracy j)+Real.log (1/ρ))
    (screenLevel ρ j) ρ q hq hmass
  have h₀ := mul_le_mul_of_nonneg_left
    (screenThreshold_error (screenLevel ρ j) (screenAccuracy j) (screenAccuracy_pos j)) hρ.le
  have h₁ := asymmetricThreshold_error (screenLevel ρ j) (screenAccuracy j) ρ (screenAccuracy_pos j) hρ
  have hg := screenLevel_gaussian ρ hρ hρ1 j
  have hpos : 0 < ρ*screenAccuracy j := mul_pos hρ (screenAccuracy_pos j)
  nlinarith

end ThresholdHC.CriticalUpper
