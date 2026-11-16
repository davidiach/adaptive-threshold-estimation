import ThresholdHC.PowerWindow.Specification

noncomputable section
open MeasureTheory Set
namespace ThresholdHC.PowerWindow

theorem quantile_scale_pos {α ρ : ℝ} (hρ : 0 < ρ) : 0 < powerQuantileScale α ρ :=
  Real.rpow_pos_of_pos hρ _

theorem quantile_scale_lt_one {α ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    powerQuantileScale α ρ < 1 :=
  Real.rpow_lt_one hρ.le hρ1 (by positivity)

theorem power_phi_closed : PowerPhiStatement := by
  intro α ρ hα hρ hρ1
  have hs : 0 < powerQuantileScale α ρ := quantile_scale_pos hρ
  have hs1 : powerQuantileScale α ρ < 1 := quantile_scale_lt_one hα hρ hρ1
  by_cases htwo : α = 2
  · subst α
    rw [ite_eq_left (show (2 : ℝ) = 2 from rfl)]
    simp only [powerPhi, show (2 : ℝ) - 3 = -1 by norm_num, Real.rpow_neg_one]
    rw [integral_inv_of_pos hs (by norm_num), one_div, Real.log_inv]
    unfold powerQuantileScale
    rw [Real.log_rpow hρ]
    simp only [one_div, Real.log_inv]
    ring
  · rw [ite_eq_right htwo]
    unfold powerPhi
    rw [integral_rpow (Or.inr ⟨by intro he; apply htwo; linarith,
      notMem_uIcc_of_lt hs (by norm_num)⟩)]
    have he : α - 3 + 1 = α - 2 := by ring
    have hp : powerQuantileScale α ρ ^ (α - 2) = ρ ^ (1 - 2 / α) := by
      unfold powerQuantileScale
      rw [← Real.rpow_mul hρ.le]
      congr 1
      field_simp
    rw [he, Real.one_rpow, hp]
    ring

theorem power_phi_pos {α ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    0 < powerPhi α ρ := by
  unfold powerPhi
  apply mul_pos hα
  apply intervalIntegral.integral_pos (quantile_scale_lt_one hα hρ hρ1)
  · exact (continuousOn_id.rpow_const (fun x hx => Or.inl
      ((quantile_scale_pos hρ).trans_le hx.1).ne'))
  · intro x hx
    exact (Real.rpow_pos_of_pos ((quantile_scale_pos hρ).trans hx.1) _).le
  · exact ⟨powerQuantileScale α ρ, ⟨le_rfl, (quantile_scale_lt_one hα hρ hρ1).le⟩,
      Real.rpow_pos_of_pos (quantile_scale_pos hρ) _⟩

end ThresholdHC.PowerWindow
