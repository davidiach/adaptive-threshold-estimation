
import ThresholdHC.AnytimeLower.TailSelection
import ThresholdHC.HardBudget.SelectionScale

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier6

def normalizedSelection (μ : Measure Gap) (ρ B : ℝ) : ℝ :=
  sqrt B*(ThresholdHC.EntropyTail.selection μ ρ B).toReal

def selectionCoefficients (μ : Measure Gap) (ρ : ℝ) : Set ℝ :=
  {c | ∃ B : ℝ, 0 < B ∧ c = normalizedSelection μ ρ B}

def selectionCoefficient (μ : Measure Gap) (ρ : ℝ) : ℝ :=
  sSup (selectionCoefficients μ ρ)

theorem selectionCoefficients_nonempty (μ : Measure Gap) (ρ : ℝ) :
    (selectionCoefficients μ ρ).Nonempty :=
  ⟨normalizedSelection μ ρ 1,1,by norm_num,rfl⟩

theorem normalizedSelection_le_inverse (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hI : Integrable (fun d : Gap => (d:ℝ)⁻¹) μ) (ρ : ℝ) {B : ℝ} (hB : 0 < B) :
    normalizedSelection μ ρ B ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂μ := by
  let h := 1/sqrt B
  have hh : 0 < h := one_div_pos.mpr (sqrt_pos.mpr hB)
  have htail : ThresholdHC.EntropyTailQuantile.tailModulus μ h ≤
      h*(∫ d : Gap, (d:ℝ)⁻¹ ∂μ) := by
    have hi := integral_mono (ThresholdHC.EntropyTailQuantile.tailKernel_integrable μ hh.le)
      (hI.const_mul h) (fun d => by
        simpa only [div_eq_mul_inv] using min_le_right (1:ℝ) (h/(d:ℝ)))
    simpa only [ThresholdHC.EntropyTailQuantile.tailModulus,integral_const_mul] using hi
  have he := ThresholdHC.EntropyTail.selection_le_objective (Measure.zero_le μ) ρ B
  rw [ThresholdHC.EntropyTail.selectionObjective_zero,
    ← ThresholdHC.EntropyTail.quantile_tailModulus_eq μ hh.le] at he
  have hnn : 0 ≤ h*(∫ d : Gap, (d:ℝ)⁻¹ ∂μ) :=
    mul_nonneg hh.le (integral_nonneg (fun d => inv_nonneg.mpr d.property.1.le))
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top (he.trans (ENNReal.ofReal_le_ofReal htail))
  rw [ENNReal.toReal_ofReal hnn] at hr
  have hs := mul_le_mul_of_nonneg_left hr (sqrt_nonneg B)
  change normalizedSelection μ ρ B ≤ _ at hs
  have hid : sqrt B*(h*(∫ d : Gap, (d:ℝ)⁻¹ ∂μ)) = ∫ d : Gap, (d:ℝ)⁻¹ ∂μ := by
    dsimp [h]
    field_simp [(sqrt_pos.mpr hB).ne']
  exact hs.trans_eq hid

theorem selectionCoefficients_bddAbove (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hI : Integrable (fun d : Gap => (d:ℝ)⁻¹) μ) (ρ : ℝ) :
    BddAbove (selectionCoefficients μ ρ) := by
  refine ⟨∫ d : Gap, (d:ℝ)⁻¹ ∂μ,?_⟩
  rintro c ⟨B,hB,rfl⟩
  exact normalizedSelection_le_inverse μ hI ρ hB

theorem normalizedSelection_le_coefficient (μ : Measure Gap)
    (ρ : ℝ) (hb : BddAbove (selectionCoefficients μ ρ)) {B : ℝ} (hB : 0 < B) :
    normalizedSelection μ ρ B ≤ selectionCoefficient μ ρ :=
  le_csSup hb ⟨B,hB,rfl⟩

theorem selectionCoefficient_pos (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hb : BddAbove (selectionCoefficients μ ρ)) : 0 < selectionCoefficient μ ρ := by
  have he := normalizedSelection_le_coefficient μ ρ hb (show (0:ℝ) < 1 by norm_num)
  have hsat := ThresholdHC.HardBudget.selection_saturates μ hρ hρ1
    (show (0:ℝ) < 1 by norm_num) (show (1:ℝ) < 4 by norm_num)
  simp only [normalizedSelection,sqrt_one,one_mul,hsat,ENNReal.toReal_ofReal hρ.le] at he
  exact hρ.trans_le he

theorem exists_coefficient_witness (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hb : BddAbove (selectionCoefficients μ ρ)) :
    ∃ B : ℝ, 0 < B ∧ selectionCoefficient μ ρ/2 < normalizedSelection μ ρ B := by
  have hp := selectionCoefficient_pos μ hρ hρ1 hb
  have hh : selectionCoefficient μ ρ/2 < sSup (selectionCoefficients μ ρ) := by
    change selectionCoefficient μ ρ/2 < selectionCoefficient μ ρ
    linarith
  obtain ⟨c,⟨B,hB,rfl⟩,hc⟩ := (lt_csSup_iff hb (selectionCoefficients_nonempty μ ρ)).mp hh
  exact ⟨B,hB,hc⟩

end ThresholdHC.AnytimeLower
