import ThresholdHC.ArbitraryLawAdaptation.SelectionLift

/-! The square-root-three comparison for the original infimum over all
fractional selections, under a supplied increasing-gap coupling. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

theorem one_le_sqrt_three : (1 : ℝ) ≤ Real.sqrt 3 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have h0 := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

theorem transportedSelection_objective (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    (hup : ∀ᵐ z ∂π, (z.1 : ℝ) ≤ (z.2 : ℝ))
    {σ : Measure Gap} (hσ : σ ≤ π.map Prod.fst) (ρ B : ℝ) :
    selectionObjective (π.map Prod.snd) ρ B (transportedSelection π σ) ≤
      ENNReal.ofReal (Real.sqrt 3)*selectionObjective (π.map Prod.fst) ρ B σ := by
  have hc := transportedSelection_costs π hup hσ (h := 1/Real.sqrt B) (by positivity)
  have hroot : (3 : ℝ≥0∞)^(1/2 : ℝ) = ENNReal.ofReal (Real.sqrt 3) := by
    rw [← ENNReal.ofReal_ofNat, ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num),
      ← Real.sqrt_eq_rpow]
  have hge : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.sqrt 3) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal one_le_sqrt_three
  unfold selectionObjective
  rw [mul_add]
  apply add_le_add
  · calc
      _ ≤ ENNReal.ofReal (1/Real.sqrt B) *
          (ENNReal.ofReal ρ*(3*gamma σ))^(1/2 : ℝ) :=
        mul_le_mul_right (ENNReal.rpow_le_rpow (mul_le_mul_right hc.1 _) (by norm_num)) _
      _ = _ := by
        rw [mul_left_comm (ENNReal.ofReal ρ), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hroot]
        ac_rfl
  · exact hc.2.trans (by
      simpa only [one_mul] using
        mul_le_mul_left hge (tailCost (π.map Prod.fst-σ) (1/Real.sqrt B)))

theorem selection_le_sqrt_three_of_increasing_coupling (π : Measure (Gap × Gap))
    [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1 : ℝ) ≤ (z.2 : ℝ)) (ρ B : ℝ) :
    selection (π.map Prod.snd) ρ B ≤
      ENNReal.ofReal (Real.sqrt 3)*selection (π.map Prod.fst) ρ B := by
  have hge : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.sqrt 3) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal one_le_sqrt_three
  have hne := ne_of_gt (lt_of_lt_of_le zero_lt_one hge)
  conv_rhs => rw [selection, mul_min]
  apply le_min
  · exact (selection_le_rho _ _ _).trans
      (by simpa only [one_mul] using mul_le_mul_left hge (ENNReal.ofReal ρ))
  · rw [ENNReal.mul_iInf_of_ne hne ENNReal.ofReal_ne_top]
    refine le_iInf fun σ => ?_
    rw [ENNReal.mul_iInf_of_ne hne ENNReal.ofReal_ne_top]
    refine le_iInf fun hσ => ?_
    exact (selection_le_objective (transportedSelection_le π hσ) ρ B).trans
      (transportedSelection_objective π hup hσ ρ B)

end ThresholdHC.ArbitraryLawAdaptation
