import ThresholdHC.EntropyTail.Objective
import ThresholdHC.PsiSelection.Specification

/-! The deterministic comparison `Ψ ≤ K`.

Fix a feasible allocation `v` and a submeasure `σ ≤ μ`. On `μ - σ` the `Ψ`
integrand `min{v, h√v/d}` is at most the truncated inverse-gap cost
`min{1, h/d}`. On `σ` it is at most `h√v/d`, and Cauchy–Schwarz bounds its
integral by `h √(∫ v dσ) √(∫ d^{-2} dσ) ≤ h √(ρ Γ_σ)`. The integrand is also at
most `v`, so the value is at most `ρ`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.PsiSelection
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTail

theorem ofReal_sqrt_sq (x : ℝ) :
    ENNReal.ofReal (Real.sqrt x) ^ (2 : ℝ) = ENNReal.ofReal x := by
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg x) (by norm_num)]
  by_cases hx : 0 ≤ x
  · congr 1
    rw [Real.rpow_two, Real.sq_sqrt hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [Real.sqrt_eq_zero_of_nonpos hx', ENNReal.ofReal_of_nonpos hx']
    simp

/-- For every feasible allocation the `Ψ` objective is at most `ρ` and at most
the selection objective of every submeasure. -/
theorem rareObjective_le (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ h : ℝ} (hh : 0 < h) {v : Gap → ℝ} (hv : Tier3.FeasibleAllocation μ ρ v) :
    ENNReal.ofReal (Tier3.rareObjective μ (fun d : Gap => (d : ℝ)) h v) ≤ ENNReal.ofReal ρ ∧
    ∀ σ : Measure Gap, σ ≤ μ →
      ENNReal.ofReal (Tier3.rareObjective μ (fun d : Gap => (d : ℝ)) h v) ≤
        ENNReal.ofReal h * (ENNReal.ofReal ρ * gamma σ) ^ (1/2 : ℝ) + tailCost (μ - σ) h := by
  obtain ⟨hvm, hv01, hvρ⟩ := hv
  let f : Gap → ℝ := fun d => min (v d) (h * Real.sqrt (v d) / (d : ℝ))
  have hfm : Measurable f :=
    hvm.min ((measurable_const.mul hvm.sqrt).div measurable_subtype_coe)
  have hobj : Tier3.rareObjective μ (fun d : Gap => (d : ℝ)) h v = ∫ d, f d ∂μ := rfl
  have hf0 : ∀ᵐ d ∂μ, 0 ≤ f d := hv01.mono fun d hd =>
    le_min hd.1 (div_nonneg (mul_nonneg hh.le (Real.sqrt_nonneg _)) d.2.1.le)
  have hfv : ∀ d, f d ≤ v d := fun d => min_le_left _ _
  have hvi : Integrable v μ :=
    (integrable_const (1 : ℝ)).mono' hvm.aestronglyMeasurable
      (hv01.mono fun d hd => by rw [Real.norm_eq_abs, abs_of_nonneg hd.1]; exact hd.2)
  have hfi : Integrable f μ :=
    (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
      (by
        filter_upwards [hv01, hf0] with d hd hd0
        rw [Real.norm_eq_abs, abs_of_nonneg hd0]
        exact (hfv d).trans hd.2)
  have hlin : ENNReal.ofReal (∫ d, f d ∂μ) = ∫⁻ d, ENNReal.ofReal (f d) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hfi hf0
  have hvlin : ∫⁻ d, ENNReal.ofReal (v d) ∂μ ≤ ENNReal.ofReal ρ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hvi (hv01.mono fun d hd => hd.1)]
    exact ENNReal.ofReal_le_ofReal hvρ
  rw [hobj]
  refine ⟨?_, fun σ hσ => ?_⟩
  · exact ENNReal.ofReal_le_ofReal
      ((integral_mono_ae hfi hvi (Filter.Eventually.of_forall hfv)).trans hvρ)
  · have : IsFiniteMeasure σ := ⟨(hσ Set.univ).trans_lt (measure_lt_top μ _)⟩
    have hsplit : ∫⁻ d, ENNReal.ofReal (f d) ∂μ =
        ∫⁻ d, ENNReal.ofReal (f d) ∂(μ - σ) + ∫⁻ d, ENNReal.ofReal (f d) ∂σ := by
      rw [← lintegral_add_measure, Measure.sub_add_cancel_of_le hσ]
    -- The unselected part pays the truncated inverse-gap cost.
    have htail : ∫⁻ d, ENNReal.ofReal (f d) ∂(μ - σ) ≤ tailCost (μ - σ) h := by
      unfold tailCost
      refine lintegral_mono_ae ?_
      have hv' : ∀ᵐ d ∂(μ - σ), 0 ≤ v d ∧ v d ≤ 1 :=
        hv01.filter_mono (ae_mono Measure.sub_le)
      filter_upwards [hv'] with d hd
      refine ENNReal.ofReal_le_ofReal (le_min ((hfv d).trans hd.2) ?_)
      refine (min_le_right _ _).trans ?_
      have hs : Real.sqrt (v d) ≤ 1 := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt hd.2
      exact div_le_div_of_nonneg_right (by nlinarith) d.2.1.le
    -- The selected part pays the entropy cost, by Cauchy–Schwarz.
    have hcore : ∫⁻ d, ENNReal.ofReal (f d) ∂σ ≤
        ENNReal.ofReal h * (ENNReal.ofReal ρ * gamma σ) ^ (1/2 : ℝ) := by
      let a : Gap → ℝ≥0∞ := fun d => ENNReal.ofReal (Real.sqrt (v d))
      let b : Gap → ℝ≥0∞ := fun d => ENNReal.ofReal ((d : ℝ)⁻¹)
      have ham : Measurable a := hvm.sqrt.ennreal_ofReal
      have hbm : Measurable b := (measurable_subtype_coe.inv).ennreal_ofReal
      have hpt : ∀ d, ENNReal.ofReal (f d) ≤ ENNReal.ofReal h * (a * b) d := by
        intro d
        have hd := d.2.1
        calc ENNReal.ofReal (f d)
            ≤ ENNReal.ofReal (h * Real.sqrt (v d) / (d : ℝ)) :=
              ENNReal.ofReal_le_ofReal (min_le_right _ _)
          _ = ENNReal.ofReal h * (a * b) d := by
              simp only [a, b, Pi.mul_apply]
              rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul hh.le]
              congr 1
              field_simp
      have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq σ Real.HolderConjugate.two_two
        ham.aemeasurable hbm.aemeasurable
      have ha2 : ∫⁻ d, a d ^ (2 : ℝ) ∂σ ≤ ENNReal.ofReal ρ := by
        calc ∫⁻ d, a d ^ (2 : ℝ) ∂σ = ∫⁻ d, ENNReal.ofReal (v d) ∂σ :=
              lintegral_congr fun d => ofReal_sqrt_sq (v d)
          _ ≤ ∫⁻ d, ENNReal.ofReal (v d) ∂μ := lintegral_mono' hσ le_rfl
          _ ≤ ENNReal.ofReal ρ := hvlin
      have hb2 : ∫⁻ d, b d ^ (2 : ℝ) ∂σ ≤ gamma σ := by
        refine le_trans (le_of_eq (lintegral_congr fun d => ?_)) (lintegral_le_gamma σ)
        simp only [b]
        rw [ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 d.2.1.le) (by norm_num), Real.rpow_two]
      calc ∫⁻ d, ENNReal.ofReal (f d) ∂σ
          ≤ ∫⁻ d, ENNReal.ofReal h * (a * b) d ∂σ := lintegral_mono hpt
        _ = ENNReal.ofReal h * ∫⁻ d, (a * b) d ∂σ :=
            lintegral_const_mul _ (ham.mul hbm)
        _ ≤ ENNReal.ofReal h *
              ((∫⁻ d, a d ^ (2 : ℝ) ∂σ) ^ (1 / (2 : ℝ)) * (∫⁻ d, b d ^ (2 : ℝ) ∂σ) ^ (1 / (2 : ℝ))) :=
            by gcongr
        _ ≤ ENNReal.ofReal h *
              ((ENNReal.ofReal ρ) ^ (1 / (2 : ℝ)) * (gamma σ) ^ (1 / (2 : ℝ))) := by
            gcongr
        _ = ENNReal.ofReal h * (ENNReal.ofReal ρ * gamma σ) ^ (1/2 : ℝ) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1/2)]
    rw [hlin, hsplit, add_comm]
    exact add_le_add hcore htail

/-- `Ψ_{μ,ρ}(h) ≤ K_{μ,ρ}(h^{-2})` in the scale form used by both statistical
corollaries: any positive resolution `h = 1/√b`. -/
theorem rarePsi_le_selection_scale (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) {b : ℝ} (hb : 0 < b) :
    rarePsi μ ρ (1 / Real.sqrt b) ≤ selection μ ρ b := by
  have hh : 0 < 1 / Real.sqrt b := by positivity
  unfold rarePsi selection
  refine iSup₂_le fun v hv => le_min (rareObjective_le μ hh hv).1 (le_iInf₂ fun σ hσ => ?_)
  exact (rareObjective_le μ hh hv).2 σ hσ

end ThresholdHC.PsiSelection
