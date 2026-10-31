import ThresholdHC.StoppingProgram.ConeLagrange

/-! Weak four-prior duality for the actual robust flow program. Infinite
information ratios and the zero positive-part numerator are included. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem certificate_lagrange {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hB : 0 ≤ B) (Q : FourPriors) (hQ : Admissible μ ρ Q)
    (C : Certificate N) (hC : Feasible μ ρ B C) (hK : informationRatio μ N Q ≠ ⊤)
    {α : ℝ} (hα : 0 ≤ α) :
    α*(signMean μ Q.high.val-signMean μ Q.low.val)-
      α^2*(1+B*(informationRatio μ N Q).toReal/4) ≤ C.bias^2+C.variance := by
  have hh := (abs_le.mp (hC.bias_bound Q.high hQ.2.1)).1
  have hl := (abs_le.mp (hC.bias_bound Q.low hQ.1)).2
  have hd : signMean μ Q.high.val-signMean μ Q.low.val ≤
      2*C.bias+countMean μ Q.high C.flow.outputWeight-countMean μ Q.low C.flow.outputWeight := by
    linarith
  have hi := flowInformation_toReal_le μ Q C.flow hC.cone hK hB
    (hC.work_bound Q.work hQ.2.2.2)
  have hc := flow_cone_lagrange μ Q C.flow hC.cone
    (flowInformation_finite_of_ratio_finite μ Q C.flow hC.cone hK) α
  have hv := hC.variance_bound Q.variance hQ.2.2.1
  have hd' := mul_le_mul_of_nonneg_left hd hα
  have hi' := mul_le_mul_of_nonneg_left hi (sq_nonneg α)
  nlinarith [sq_nonneg (C.bias-α)]

theorem dualRatio_le_certificate {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hB : 0 < B) (Q : FourPriors) (hQ : Admissible μ ρ Q)
    (C : Certificate N) (hC : Feasible μ ρ B C) :
    dualRatio μ B N Q ≤ certificateSquared C := by
  by_cases hK : informationRatio μ N Q = ⊤
  · simp only [dualRatio,hK,ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hB),
      add_top,ENNReal.div_top]
    exact zero_le
  by_cases hD : signMean μ Q.high.val-signMean μ Q.low.val ≤ 0
  · simp only [dualRatio,ENNReal.ofReal_of_nonpos hD,zero_pow (by decide : (2:ℕ) ≠ 0),
      ENNReal.zero_div]
    exact zero_le
  have hD' : 0 < signMean μ Q.high.val-signMean μ Q.low.val := lt_of_not_ge hD
  let K := (informationRatio μ N Q).toReal
  let D := 4+B*K
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  have hD0 : 0 < D := by dsimp [D]; positivity
  have he : (2*(signMean μ Q.high.val-signMean μ Q.low.val)/D)*
      (signMean μ Q.high.val-signMean μ Q.low.val)-
      (2*(signMean μ Q.high.val-signMean μ Q.low.val)/D)^2*(1+B*K/4) =
      (signMean μ Q.high.val-signMean μ Q.low.val)^2/D := by
    dsimp [D]
    field_simp
    ring
  have hr := certificate_lagrange μ hB.le Q hQ C hC hK
    (α := 2*(signMean μ Q.high.val-signMean μ Q.low.val)/D) (by positivity)
  change _ - _*(1+B*K/4) ≤ _ at hr
  rw [he] at hr
  have hden : 4+ENNReal.ofReal B*informationRatio μ N Q = ENNReal.ofReal D := by
    rw [← ENNReal.ofReal_toReal hK,← ENNReal.ofReal_mul hB.le,← ENNReal.ofReal_ofNat 4,
      ← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 4) (mul_nonneg hB.le hK0)]
  rw [dualRatio,hden,← ENNReal.ofReal_pow hD'.le,
    ← ENNReal.ofReal_div_of_pos hD0]
  exact ENNReal.ofReal_le_ofReal hr

theorem weak_duality (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}
    (hB : 0 < B) (N : ℕ) : dualValue μ ρ B N ≤ programSquared μ ρ B N := by
  apply iSup_le
  intro Q
  apply iSup_le
  intro hQ
  apply le_sInf
  rintro x ⟨C,hC,rfl⟩
  exact dualRatio_le_certificate μ hB Q hQ C hC

end ThresholdHC.StoppingProgram
