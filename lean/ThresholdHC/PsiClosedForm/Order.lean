import ThresholdHC.PsiClosedForm.Specification
import ThresholdHC.PsiSelection.Comparison
import ThresholdHC.EntropyTail.Gamma
import ThresholdHC.EntropyTail.Bridge
import ThresholdHC.EntropyTailQuantile.QuantileSplit

/-! The elementary comparisons of display (W1) and the upper half of (W2).

`A_σ ≤ Γ_σ` gives `K⁰ ≤ K` and `Q⁰ ≤ Q`. The choice `σ = κ`, whose complement
in `μ` is the quantile tail, gives `K⁰ ≤ Q⁰`. The proof of `Ψ ≤ K` bounds the
selected part by Cauchy–Schwarz with `∫ d^{-2} dσ` before weakening it to
`Γ_σ`; keeping that integral gives `Ψ ≤ K⁰`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.PsiClosedForm
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTail

theorem inverseSquareCost_le_gamma (σ : Measure Gap) : inverseSquareCost σ ≤ gamma σ :=
  lintegral_le_gamma σ

theorem selectionZero_le_selection (μ : Measure Gap) (ρ B : ℝ) :
    selectionZero μ ρ B ≤ selection μ ρ B := by
  unfold selectionZero selection selectionObjective
  refine min_le_min le_rfl (iInf₂_mono fun σ _ => add_le_add ?_ le_rfl)
  gcongr
  exact inverseSquareCost_le_gamma σ

theorem quantileCore_le (μ : Measure Gap) (ρ : ℝ) :
    ThresholdHC.EntropyTailQuantile.quantileCore μ ρ ≤ μ := by
  unfold ThresholdHC.EntropyTailQuantile.quantileCore
  exact Measure.sub_le

theorem quantileZero_le_closedQuantile (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℝ) :
    quantileZero μ ρ B ≤ ThresholdHC.EntropyTailQuantile.closedQuantileValue μ ρ B := by
  have hν : IsFiniteMeasure (ThresholdHC.EntropyTailQuantile.quantileTail μ ρ) :=
    isFiniteMeasure_of_le μ (ThresholdHC.EntropyTailQuantile.quantileTail_le μ hρ hρ1)
  have hκ : IsFiniteMeasure (ThresholdHC.EntropyTailQuantile.quantileCore μ ρ) :=
    isFiniteMeasure_of_le μ (quantileCore_le μ ρ)
  have hh : (0 : ℝ) ≤ 1 / Real.sqrt B := by positivity
  have e : (Real.sqrt B)⁻¹ = 1 / Real.sqrt B := (one_div _).symm
  unfold quantileZero ThresholdHC.EntropyTailQuantile.closedQuantileValue
    ThresholdHC.EntropyTailQuantile.budgetScale
  rw [e, quantile_tailModulus_eq _ hh]
  refine min_le_min le_rfl (add_le_add le_rfl ?_)
  gcongr
  exact (inverseSquareCost_le_gamma _).trans (gamma_le_quantile_measureCostEntropy _)

/-- The complement of the quantile core in `μ` is the quantile tail. -/
theorem sub_quantileCore (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    μ - ThresholdHC.EntropyTailQuantile.quantileCore μ ρ =
      ThresholdHC.EntropyTailQuantile.quantileTail μ ρ := by
  have hκ : IsFiniteMeasure (ThresholdHC.EntropyTailQuantile.quantileCore μ ρ) :=
    isFiniteMeasure_of_le μ (quantileCore_le μ ρ)
  have h := ThresholdHC.EntropyTailQuantile.quantileTail_add_core μ hρ hρ1
  have key : ThresholdHC.EntropyTailQuantile.quantileTail μ ρ +
      ThresholdHC.EntropyTailQuantile.quantileCore μ ρ -
        ThresholdHC.EntropyTailQuantile.quantileCore μ ρ =
      ThresholdHC.EntropyTailQuantile.quantileTail μ ρ := Measure.add_sub_cancel
  rwa [h] at key

theorem selectionZero_le_quantileZero (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℝ) :
    selectionZero μ ρ B ≤ quantileZero μ ρ B := by
  unfold selectionZero quantileZero
  refine min_le_min le_rfl
    ((iInf₂_le (ThresholdHC.EntropyTailQuantile.quantileCore μ ρ) (quantileCore_le μ ρ)).trans ?_)
  rw [sub_quantileCore μ hρ hρ1, add_comm]

/-- For every feasible allocation the `Ψ` objective is at most the entropy-free
selection objective of every submeasure. -/
theorem rareObjective_le_zero (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ h : ℝ} (hh : 0 < h) {v : Gap → ℝ} (hv : Tier3.FeasibleAllocation μ ρ v)
    (σ : Measure Gap) (hσ : σ ≤ μ) :
    ENNReal.ofReal (Tier3.rareObjective μ (fun d : Gap => (d : ℝ)) h v) ≤
      ENNReal.ofReal h * (ENNReal.ofReal ρ * inverseSquareCost σ) ^ (1/2 : ℝ)
        + tailCost (μ - σ) h := by
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
  have : IsFiniteMeasure σ := ⟨(hσ Set.univ).trans_lt (measure_lt_top μ _)⟩
  have hsplit : ∫⁻ d, ENNReal.ofReal (f d) ∂μ =
      ∫⁻ d, ENNReal.ofReal (f d) ∂(μ - σ) + ∫⁻ d, ENNReal.ofReal (f d) ∂σ := by
    rw [← lintegral_add_measure, Measure.sub_add_cancel_of_le hσ]
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
  have hcore : ∫⁻ d, ENNReal.ofReal (f d) ∂σ ≤
      ENNReal.ofReal h * (ENNReal.ofReal ρ * inverseSquareCost σ) ^ (1/2 : ℝ) := by
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
            lintegral_congr fun d => ThresholdHC.PsiSelection.ofReal_sqrt_sq (v d)
        _ ≤ ∫⁻ d, ENNReal.ofReal (v d) ∂μ := lintegral_mono' hσ le_rfl
        _ ≤ ENNReal.ofReal ρ := hvlin
    have hb2 : ∫⁻ d, b d ^ (2 : ℝ) ∂σ = inverseSquareCost σ := by
      unfold inverseSquareCost
      refine lintegral_congr fun d => ?_
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
            ((ENNReal.ofReal ρ) ^ (1 / (2 : ℝ)) * (inverseSquareCost σ) ^ (1 / (2 : ℝ))) := by
          rw [hb2]
          gcongr
      _ = ENNReal.ofReal h * (ENNReal.ofReal ρ * inverseSquareCost σ) ^ (1/2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1/2)]
  rw [hlin, hsplit, add_comm]
  exact add_le_add hcore htail

/-- `Ψ_{μ,ρ}(B^{-1/2}) ≤ K⁰_{μ,ρ}(B)`. -/
theorem rarePsi_le_selectionZero (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) {B : ℝ} (hB : 0 < B) :
    rarePsi μ ρ (1 / Real.sqrt B) ≤ selectionZero μ ρ B := by
  have hh : 0 < 1 / Real.sqrt B := by positivity
  unfold rarePsi selectionZero
  refine iSup₂_le fun v hv =>
    le_min (ThresholdHC.PsiSelection.rareObjective_le μ hh hv).1 (le_iInf₂ fun σ hσ => ?_)
  exact rareObjective_le_zero μ hh hv σ hσ

end ThresholdHC.PsiClosedForm
