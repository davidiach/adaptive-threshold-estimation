import ThresholdHC.Proofs.Tier2.Information

noncomputable section
namespace ThresholdHC.Tier3
open MeasureTheory Real
open ThresholdHC.Proofs

theorem integral_support {U : Type} [MeasurableSpace U] (μ : Measure U)
    (P Q : U → ℝ) (hP : ∀ u, 0 ≤ P u) (hQ : ∀ u, 0 ≤ Q u)
    (hPi : Integrable P μ) (hQi : Integrable Q μ)
    (hPQ : ∀ u, Q u = 0 → P u = 0) (hq0 : ∫ u, Q u ∂μ = 0) :
    ∫ u, P u ∂μ = 0 := by
  have hq := (integral_eq_zero_iff_of_nonneg hQ hQi).mp hq0
  apply (integral_eq_zero_iff_of_nonneg hP hPi).mpr
  filter_upwards [hq] with u hu
  exact hPQ u hu

theorem integral_log_sum {U : Type} [MeasurableSpace U] (μ : Measure U)
    (P Q : U → ℝ) (hP : ∀ u, 0 ≤ P u) (hQ : ∀ u, 0 ≤ Q u)
    (hPi : Integrable P μ) (hQi : Integrable Q μ)
    (hPQ : ∀ u, Q u = 0 → P u = 0)
    (hKi : Integrable (fun u => P u * Real.log (P u / Q u)) μ) :
    (∫ u, P u ∂μ) * Real.log ((∫ u, P u ∂μ)/(∫ u, Q u ∂μ)) ≤
      ∫ u, P u * Real.log (P u / Q u) ∂μ := by
  have hp : 0 ≤ ∫ u, P u ∂μ := integral_nonneg hP
  have hq : 0 ≤ ∫ u, Q u ∂μ := integral_nonneg hQ
  by_cases hp0 : ∫ u, P u ∂μ = 0
  · have hpzero := (integral_eq_zero_iff_of_nonneg hP hPi).mp hp0
    have hkzero : (fun u => P u * Real.log (P u / Q u)) =ᵐ[μ] 0 := by
      filter_upwards [hpzero] with u hu
      simp [hu]
    rw [hp0, zero_mul, integral_congr_ae hkzero]
    simp
  have hp' : 0 < ∫ u, P u ∂μ := lt_of_le_of_ne hp (Ne.symm hp0)
  have hq' : 0 < ∫ u, Q u ∂μ := by
    by_contra h
    have hzero := le_antisymm (not_lt.mp h) hq
    exact hp0 (integral_support μ P Q hP hQ hPi hQi hPQ hzero)
  have hleft := ((hPi.mul_const (Real.log ((∫ u, P u ∂μ)/(∫ u, Q u ∂μ)))).add hPi).sub
    (hQi.const_mul ((∫ u, P u ∂μ)/(∫ u, Q u ∂μ)))
  have h := integral_mono hleft hKi (fun u =>
    Tier2Information.kl_supporting_line (P u) (Q u) _ _ (hP u) (hQ u) (hPQ u) hp' hq')
  simp only [Pi.sub_apply, Pi.add_apply] at h
  have hs := integral_sub
    (f := fun u => P u * Real.log ((∫ u, P u ∂μ)/(∫ u, Q u ∂μ)) + P u)
    (g := fun u => ((∫ u, P u ∂μ)/(∫ u, Q u ∂μ))*Q u)
    ((hPi.mul_const _).add hPi) (hQi.const_mul _)
  have ha := integral_add (f := fun u => P u * Real.log ((∫ u, P u ∂μ)/(∫ u, Q u ∂μ)))
    (g := P) (hPi.mul_const _) hPi
  rw [hs, ha, integral_mul_const, integral_const_mul,
    div_mul_cancel₀ _ hq'.ne', add_sub_cancel_right] at h
  exact h

end ThresholdHC.Tier3
