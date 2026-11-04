import ThresholdHC.QuantileSelection.MeasureEntropy
import ThresholdHC.QuantileSelection.SeparatedCost
import ThresholdHC.QuantileSelection.Price
import ThresholdHC.EntropyTailQuantile.QuantileComparison

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal
namespace ThresholdHC.QuantileSelection
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile

/-- Compare the quantile candidate with any individual submeasure, before taking the infimum. -/
theorem comparison_pointwise (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hB : 0 < B)
    (hht : budgetScale B < quantileThreshold μ ρ) (σ : Measure Gap) (hσ : σ ≤ μ) :
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (8/5) * selectionCost μ σ ρ (budgetScale B) := by
  let t := quantileThreshold μ ρ
  let h := budgetScale B
  let r := quantileBoundaryFraction μ ρ
  have ht : 0 < t := (quantileThreshold_properties μ hρ hρ1).1
  have hh : 0 < h := budgetScale_pos hB
  have hr := quantileBoundaryFraction_properties μ hρ hρ1
  by_cases hinf : measureCostEntropy σ = ⊤
  · simp [selectionCost, hinf, ENNReal.mul_top, ENNReal.ofReal_eq_zero,
      not_le.mpr hρ, not_le.mpr (budgetScale_pos hB)]
  let L := lowerCut t r σ
  let V := upperCut t r σ
  let D := lowerCut t r (μ-σ)
  let Z := upperCut t r (μ-σ)
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le μ hσ
  have : IsFiniteMeasure L := isFiniteMeasure_of_le σ (lowerCut_le t hr.1 hr.2.1 σ)
  have : IsFiniteMeasure V := isFiniteMeasure_of_le σ (upperCut_le t hr.1 hr.2.1 σ)
  have : IsFiniteMeasure D := isFiniteMeasure_of_le (μ-σ) (lowerCut_le t hr.1 hr.2.1 _)
  have : IsFiniteMeasure Z := isFiniteMeasure_of_le (μ-σ) (upperCut_le t hr.1 hr.2.1 _)
  have hsum : L+V = σ := lowerCut_add_upperCut t hr.1 hr.2.1 σ
  have hres : D+Z = μ-σ := lowerCut_add_upperCut t hr.1 hr.2.1 _
  have hsplit : σ+(μ-σ) = μ := (add_comm ..).trans (Measure.sub_add_cancel_of_le hσ)
  have htail : quantileTail μ ρ = L+D := by
    change lowerCut t r μ = _
    rw [← lowerCut_add, hsplit]
  have hcore : quantileCore μ ρ = V+Z := by
    rw [quantileCore_eq_upperCut μ hρ hρ1]
    exact (congrArg (upperCut t r) hsplit).symm.trans (upperCut_add t r _ _)
  have hVs := upperCut_support t r σ
  have hZs := upperCut_support t r (μ-σ)
  have hLfin := ne_top_of_le_ne_top hinf (measureCostEntropy_mono (lowerCut_le t hr.1 hr.2.1 σ))
  have hVfin := (measureCostEntropy_lt_top_of_support V ht hVs).ne
  have hCfin := (measureCostEntropy_lt_top_of_support _ ht (quantileCore_support μ ρ)).ne
  let T := tailModulus (quantileTail μ ρ) h
  let a := tailModulus D h
  let c := tailModulus Z h
  let q := h^2 * ρ
  let E := fun ξ : Measure Gap => (measureCostEntropy ξ).toReal
  let P := fun ξ : Measure Gap => sqrt (q * E ξ)
  have hq : 0 ≤ q := mul_nonneg (sq_nonneg h) hρ.le
  have hT : 0 ≤ T := tailModulus_nonneg _ hh.le
  have ha : 0 ≤ a := tailModulus_nonneg _ hh.le
  have hc : 0 ≤ c := tailModulus_nonneg _ hh.le
  have hprice (ξ : Measure Gap) (hf : measureCostEntropy ξ ≠ ⊤) :
      ENNReal.ofReal h * (ENNReal.ofReal ρ * measureCostEntropy ξ)^(1/(2:ℝ)) =
        ENNReal.ofReal (P ξ) := by
    rw [entropy_root_eq_ofReal hf hρ.le hh.le]
    dsimp only [P, q, E]
    rw [mul_assoc, sqrt_mul (sq_nonneg _), sqrt_sq hh.le]
  have hmass : L univ ≤ ENNReal.ofReal ρ :=
    (lowerCut_mono t r hσ univ).trans (quantileTail_mass μ hρ hρ1).le
  have hTu : T ≤ a + P L := by
    have hb := tailModulus_le_sqrt_entropy (le_refl L) hmass hh.le
    rw [hprice L hLfin] at hb
    have hl := (ENNReal.ofReal_le_ofReal_iff (sqrt_nonneg _)).mp hb
    dsimp only [T, a]
    rw [htail, tailModulus_add _ _ hh.le]
    linarith
  have hbudget : (P L)^2 + (P V)^2 ≤ (P σ)^2 := by
    have hb := entropy_superadditive L V
    rw [hsum] at hb
    have hb' := ENNReal.toReal_mono hinf hb
    rw [ENNReal.toReal_add hLfin hVfin] at hb'
    dsimp only [P, E]
    simp only [sq_sqrt (mul_nonneg hq ENNReal.toReal_nonneg)]
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hb' hq
  have hwork : q * E Z ≤ 2*T*c := by
    let H := ∫ d : Gap, (d:ℝ)⁻¹ ∂Z
    have hH : 0 ≤ H := integral_nonneg (fun d : Gap => inv_nonneg.mpr d.property.1.le)
    have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top (separated_cost Z ht hZs)
    change E Z ≤ (ENNReal.ofReal ((2/t)*H)).toReal at he
    rw [ENNReal.toReal_ofReal (by positivity)] at he
    have hthreshold : h*ρ/t ≤ T := quantileTail_threshold_lower μ hρ hρ1 hh.le hht
    have hceq : c = h*H := tailModulus_eq_inverseCost _ (hZs.mono (fun _ hd => hht.le.trans hd))
    calc
      _ ≤ q * ((2/t)*H) := mul_le_mul_of_nonneg_left he hq
      _ = 2*(h*ρ/t)*c := by rw [hceq]; dsimp [q]; ring
      _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_right hthreshold hc]
  have hi := core_interaction V Z ht hVs hZs
  rw [← hcore] at hi
  have hroot := core_price hq (V := E V) (Z := E Z) ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    hT hc hi hwork
  have hscalar := QuantileComparison.scalar_comparison T (P V) c hT (sqrt_nonneg _) hc
  have htri := selection_triangle hT (sqrt_nonneg _) (sqrt_nonneg _) ha hTu hbudget
  have hfinal : T + P (quantileCore μ ρ) ≤ 8/5 * (P σ + (a+c)) := by
    change P (quantileCore μ ρ) ≤ sqrt ((P V)^2+2*T*c+2*P V*sqrt (T*c)) at hroot
    linarith only [hroot, hscalar, htri]
  calc
    _ ≤ ENNReal.ofReal T + ENNReal.ofReal h *
        (ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ))^(1/(2:ℝ)) := min_le_right _ _
    _ = ENNReal.ofReal (T + P (quantileCore μ ρ)) := by
      rw [hprice _ hCfin, ENNReal.ofReal_add hT (sqrt_nonneg _)]
    _ ≤ _ := by
      apply (ENNReal.ofReal_le_ofReal hfinal).trans_eq
      rw [selectionCost, ← hres, tailModulus_add _ _ hh.le, hprice σ hinf,
        ENNReal.ofReal_mul (by norm_num : 0 ≤ (8/5:ℝ)), ENNReal.ofReal_add (sqrt_nonneg _) (add_nonneg ha hc)]

end ThresholdHC.QuantileSelection
