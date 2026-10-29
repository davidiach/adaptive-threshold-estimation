import ThresholdHC.RareAboveTwo.Margin

/-! Hölder control of the rare positive contribution. The only rarity
hypothesis is the integral of q; q need not be pointwise bounded by rho. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Tier6

theorem weighted_inverse_moment (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a s r ρ : ℝ) (ha : 0 < a) (hs : 0 < s) (hsr : s < r) (hrα : r < α)
    (hm : PowerMargin μ α a) (q : SignLaw) (hq : RarePrior μ ρ q) :
    (∫ d : Gap, (a/(d : ℝ))^s*q.val d ∂μ) ≤
      (1+1/(α/r-1))^(s/r)*ρ^(1-s/r) := by
  let θ := s/r
  have hr : 0 < r := hs.trans hsr
  have hθ : 0 < θ := div_pos hs hr
  have hθ1 : θ < 1 := (div_lt_one hr).2 hsr
  have hc := Real.HolderConjugate.inv_one_sub_inv hθ hθ1
  let f : Gap → ℝ := fun d => (a/(d : ℝ))^s
  have hf0 (d : Gap) : 0 ≤ f d := Real.rpow_nonneg (div_pos ha d.property.1).le _
  have hfm : Measurable f := by unfold f; fun_prop
  have hfp : MemLp f (ENNReal.ofReal (θ⁻¹)) μ := by
    apply (integrable_norm_rpow_iff hfm.aestronglyMeasurable
      (by simp [ENNReal.ofReal_eq_zero,not_le.mpr (inv_pos.mpr hθ)]) ENNReal.ofReal_ne_top).1
    have he (d : Gap) : ‖f d‖^(ENNReal.ofReal (θ⁻¹)).toReal = (a/(d : ℝ))^r := by
      rw [Real.norm_of_nonneg (hf0 d),ENNReal.toReal_ofReal (inv_pos.mpr hθ).le]
      dsimp [f,θ]
      rw [← Real.rpow_mul (div_pos ha d.property.1).le]
      congr 1
      field_simp
    simp_rw [he]
    exact margin_inverse_integrable μ α a r ha hr hrα hm
  have hqp : MemLp q.val (ENNReal.ofReal ((1-θ)⁻¹)) μ := by
    apply MemLp.of_bound q.property.1.aestronglyMeasurable 1
    exact ae_of_all _ (fun d => by rw [Real.norm_of_nonneg (q.property.2 d).1]; exact (q.property.2 d).2)
  have hqpow (d : Gap) : (q.val d)^((1-θ)⁻¹) ≤ q.val d := by
    have h := Real.rpow_le_rpow_of_exponent_ge' (q.property.2 d).1 (q.property.2 d).2
      (by norm_num : (0 : ℝ) ≤ 1) hc.symm.lt.le
    simpa only [Real.rpow_one] using h
  have hqi : Integrable (fun d => (q.val d)^((1-θ)⁻¹)) μ := by
    apply Integrable.of_bound (q.property.1.pow measurable_const).aestronglyMeasurable 1
    exact ae_of_all _ (fun d => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (q.property.2 d).1 _)]
      exact (hqpow d).trans (q.property.2 d).2)
  have hqI : (∫ d, (q.val d)^((1-θ)⁻¹) ∂μ) ≤ ρ := by
    apply (integral_mono hqi
      (show Integrable q.val μ from MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)
        (MemLp.of_bound q.property.1.aestronglyMeasurable 1 (ae_of_all _ (fun d => by
          rw [Real.norm_of_nonneg (q.property.2 d).1]; exact (q.property.2 d).2)))) hqpow).trans
    exact hq
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hc (ae_of_all _ hf0)
    (ae_of_all _ (fun d => (q.property.2 d).1)) hfp hqp
  have he (d : Gap) : (f d)^(θ⁻¹) = (a/(d : ℝ))^r := by
    dsimp [f,θ]
    rw [← Real.rpow_mul (div_pos ha d.property.1).le]
    congr 1
    field_simp
  simp_rw [he,one_div,inv_inv] at h
  apply h.trans
  apply mul_le_mul
  · exact Real.rpow_le_rpow (integral_nonneg (fun d => Real.rpow_nonneg (div_pos ha d.property.1).le _))
      (margin_inverse_integral μ α a r ha hr hrα hm) hθ.le
  · exact Real.rpow_le_rpow (integral_nonneg (fun d => Real.rpow_nonneg (q.property.2 d).1 _))
      hqI (sub_pos.mpr hθ1).le
  · exact Real.rpow_nonneg (integral_nonneg (fun d => Real.rpow_nonneg (q.property.2 d).1 _)) _
  · apply Real.rpow_nonneg
    have : 1 < α/r := (one_lt_div hr).2 hrα
    positivity

end ThresholdHC.RareAboveTwo
