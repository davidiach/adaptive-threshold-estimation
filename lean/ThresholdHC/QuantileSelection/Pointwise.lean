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

/-- A separated inverse-moment bound and a core price bound suffice for the
pointwise comparison. This keeps the measure decomposition and clipping
argument shared between numerical constants. -/
theorem comparison_pointwise_of_price (coeff k : ℝ) (hD : 0 ≤ coeff) (hk : 0 < k)
    (sep : ∀ (Z : Measure Gap) [IsFiniteMeasure Z] {t : ℝ}, 0 < t →
      (∀ᵐ x : Gap ∂Z, t ≤ (x:ℝ)) → measureCostEntropy Z ≤
        ENNReal.ofReal ((coeff/t)*∫ x : Gap, (x:ℝ)⁻¹ ∂Z))
    (price : ∀ (V Z : Measure Gap) [IsFiniteMeasure V] [IsFiniteMeasure Z] {t q T c : ℝ},
      0 < t → (∀ᵐ x : Gap ∂V, t ≤ (x:ℝ)) → (∀ᵐ x : Gap ∂Z, t ≤ (x:ℝ)) →
      0 ≤ q → 0 ≤ T → 0 ≤ c → q*(measureCostEntropy Z).toReal ≤ coeff*T*c →
      T + sqrt (q*(measureCostEntropy (V+Z)).toReal) ≤
        k*(sqrt (T^2+(sqrt (q*(measureCostEntropy V).toReal))^2)+c))
    (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hB : 0 < B)
    (hht : budgetScale B < quantileThreshold μ ρ) (σ : Measure Gap) (hσ : σ ≤ μ) :
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal k * selectionCost μ σ ρ (budgetScale B) := by
  let t := quantileThreshold μ ρ
  let h := budgetScale B
  let r := quantileBoundaryFraction μ ρ
  have ht : 0 < t := (quantileThreshold_properties μ hρ hρ1).1
  have hh : 0 < h := budgetScale_pos hB
  have hr := quantileBoundaryFraction_properties μ hρ hρ1
  by_cases hinf : measureCostEntropy σ = ⊤
  · simp [selectionCost, hinf, ENNReal.mul_top, ENNReal.ofReal_eq_zero,
      not_le.mpr hk, not_le.mpr hρ, not_le.mpr (budgetScale_pos hB)]
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
  have hwork : q * E Z ≤ coeff*T*c := by
    let H := ∫ d : Gap, (d:ℝ)⁻¹ ∂Z
    have hH : 0 ≤ H := integral_nonneg (fun d : Gap => inv_nonneg.mpr d.property.1.le)
    have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top (sep Z ht hZs)
    change E Z ≤ (ENNReal.ofReal ((coeff/t)*H)).toReal at he
    rw [ENNReal.toReal_ofReal (by positivity)] at he
    have hthreshold : h*ρ/t ≤ T := quantileTail_threshold_lower μ hρ hρ1 hh.le hht
    have hceq : c = h*H := tailModulus_eq_inverseCost _ (hZs.mono (fun _ hd => hht.le.trans hd))
    calc
      _ ≤ q * ((coeff/t)*H) := mul_le_mul_of_nonneg_left he hq
      _ = coeff*(h*ρ/t)*c := by rw [hceq]; dsimp [q]; ring
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hthreshold hc) hD
  have hroot := price V Z ht hVs hZs hq hT hc hwork
  have htri := selection_triangle hT (sqrt_nonneg _) (sqrt_nonneg _) ha hTu hbudget
  have hfinal : T + P (quantileCore μ ρ) ≤ k * (P σ + (a+c)) := by
    rw [hcore]
    exact hroot.trans (mul_le_mul_of_nonneg_left (by linarith only [htri] :
      sqrt (T^2+(P V)^2)+c ≤ P σ+(a+c)) hk.le)
  calc
    _ ≤ ENNReal.ofReal T + ENNReal.ofReal h *
        (ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ))^(1/(2:ℝ)) := min_le_right _ _
    _ = ENNReal.ofReal (T + P (quantileCore μ ρ)) := by
      rw [hprice _ hCfin, ENNReal.ofReal_add hT (sqrt_nonneg _)]
    _ ≤ _ := by
      apply (ENNReal.ofReal_le_ofReal hfinal).trans_eq
      rw [selectionCost, ← hres, tailModulus_add _ _ hh.le, hprice σ hinf,
        ENNReal.ofReal_mul hk.le, ENNReal.ofReal_add (sqrt_nonneg _) (add_nonneg ha hc)]

/-- Compare the quantile candidate with any individual submeasure, before taking the infimum. -/
theorem comparison_pointwise (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hB : 0 < B)
    (hht : budgetScale B < quantileThreshold μ ρ) (σ : Measure Gap) (hσ : σ ≤ μ) :
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (8/5) * selectionCost μ σ ρ (budgetScale B) := by
  apply comparison_pointwise_of_price 2 (8/5) (by norm_num) (by norm_num)
    (fun Z _ _ ht hs => separated_cost Z ht hs) _ μ hρ hρ1 hB hht σ hσ
  intro V Z _ _ t q T c ht hVs hZs hq hT hc hwork
  have hroot := core_price hq (V := (measureCostEntropy V).toReal) (Z := (measureCostEntropy Z).toReal)
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg hT hc (core_interaction V Z ht hVs hZs) hwork
  exact (add_le_add_right hroot T).trans
    (QuantileComparison.scalar_comparison T _ c hT (sqrt_nonneg _) hc)

end ThresholdHC.QuantileSelection
