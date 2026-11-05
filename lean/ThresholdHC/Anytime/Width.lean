import ThresholdHC.Anytime.Schedule
import ThresholdHC.Anytime.IntervalAlgebra

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.Anytime
open ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.HardBudget ThresholdHC.Confidence

theorem selection_antitone (μ : Measure Gap) (ρ : ℝ) {b B : ℝ} (hb : 0 < b) (hB : b ≤ B) :
    selection μ ρ B ≤ selection μ ρ b := by
  have hs : 1/sqrt B ≤ 1/sqrt b := one_div_le_one_div_of_le (sqrt_pos.mpr hb) (sqrt_le_sqrt hB)
  unfold selection
  apply min_le_min le_rfl
  apply iInf_mono; intro σ
  apply iInf_mono; intro _
  unfold selectionObjective
  apply add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal hs) le_rfl)
  apply lintegral_mono
  intro d
  exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (div_le_div_of_nonneg_right hs d.property.1.le))

theorem radius_width_bound (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B δ : ℝ}
    (hB : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) {j : ℕ} (hj : stageCount B = j+1) :
    radius μ ρ δ j ≤ 1500002*(selection μ ρ (B/inflation B δ)).toReal := by
  let L := inflation B δ
  let ℓ := log (1/stageFailure δ j)
  let β := B/L
  have hL : 0 < L := inflation_pos hB.le hd hd'
  have hℓ : 0 < ℓ := confidence_log_pos (stageFailure_pos hd j) ((stageFailure_le hd.le j).trans hd')
  have hℓL : ℓ ≤ L := stage_log_le hB.le hd hj
  have hcap := (completed_stage_bounds hB.le hj).2
  have hN : (0:ℝ) ≤ stageCap j := Nat.cast_nonneg _
  have hβ : 0 < β := div_pos hB hL
  have hβ4 : 0 < β/4 := div_pos hβ (by norm_num)
  have hb : β/4 ≤ (stageCap j:ℝ)/ℓ := by
    calc β/4 = (B/4)/L := by dsimp [β]; ring
         _ ≤ (stageCap j:ℝ)/L := div_le_div_of_nonneg_right (by linarith) hL.le
         _ ≤ _ := div_le_div_of_nonneg_left hN hℓ hℓL
  have hm := selection_antitone μ ρ hβ4 hb
  have hs := selection_budget_scale μ ρ hβ4 (by linarith : β/4 ≤ β)
  have he : sqrt (β/(β/4)) = (2:ℝ) := by field_simp; norm_num
  rw [he] at hs
  have hto := ENNReal.toReal_mono (by
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top (finite_selection μ ρ β))
    (hm.trans hs)
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by norm_num : 0 ≤ (2:ℝ))] at hto
  unfold radius
  change 750001*(selection μ ρ ((stageCap j:ℝ)/ℓ)).toReal ≤ _
  nlinarith only [hto]

variable {R : ℕ → Type} [∀ j, MeasurableSpace (R j)]

theorem all_budget_width (μ : Measure Gap) [IsProbabilityMeasure μ]
    (base : ∀ j, AdaptiveEstimator (R j)) {ρ B δ : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hB : 1 ≤ B) (hd : 0 < δ) (hd' : δ ≤ 1/4)
    (r : ∀ j, R j) (s : Table) :
    halfWidth (tableInterval base ρ (radius μ ρ δ) r s (stageCount B)) ≤
      1500002*(selection μ ρ (B/inflation B δ)).toReal := by
  have hB0 : 0 < B := by linarith
  cases he : stageCount B with
  | zero =>
    have hsmall := count_zero_small hB0.le he
    have hL1 : 1 ≤ inflation B δ := (confidence_log_ge_one hd hd').trans (inflation_ge_log hB0.le)
    have hL : 0 < inflation B δ := by linarith
    have hβ : 0 < B/inflation B δ := div_pos hB0 hL
    have hβ4 : B/inflation B δ < 4 := (div_le_self hB0.le hL1).trans_lt hsmall
    rw [selection_saturates μ hr (by linarith) hβ hβ4,ENNReal.toReal_ofReal hr.le]
    change max 0 (ρ-0)/2 ≤ _
    rw [sub_zero,max_eq_right hr.le]
    linarith
  | succ j =>
    exact (interval_width base ρ (radius μ ρ δ) r s j (radius_nonneg μ ρ δ j)).trans
      (radius_width_bound μ hB0 hd hd' he)

end ThresholdHC.Anytime
