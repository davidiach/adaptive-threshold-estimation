import ThresholdHC.SelectionStability.Specification
import ThresholdHC.EntropyTail.HardSelection
import Mathlib.MeasureTheory.Measure.TotalVariation.Basic

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace ThresholdHC.SelectionStability
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

/-- The common part leaves exactly half the variation norm in the second probability. -/
theorem common_part (μ ν : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∃ common D : Measure Gap, common ≤ μ ∧ D + common = ν ∧ D univ = ENNReal.ofReal (tvDist μ ν / 2) := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  let D := ν.restrict s - μ.restrict s
  let common := μ.restrict s + ν.restrict sᶜ
  have hD : D + μ.restrict s = ν.restrict s := Measure.sub_add_cancel_of_le hs.le_on
  have hcommon : common ≤ μ := (add_le_add le_rfl hs.ge_on_compl).trans_eq
    (Measure.restrict_add_restrict_compl hs.measurableSet)
  refine ⟨common,D,hcommon, ?_, ?_⟩
  · dsimp only [common]; rw [← add_assoc, hD, Measure.restrict_add_restrict_compl hs.measurableSet]
  · have hm := congrArg (fun ξ : Measure Gap => (ξ univ).toReal) hD
    simp only [Measure.add_apply, Measure.restrict_apply_univ, ENNReal.toReal_add
      (measure_ne_top D _) (measure_ne_top μ _)] at hm
    have hv := hs.tvDist_eq
    rw [probReal_compl_eq_one_sub hs.measurableSet, probReal_compl_eq_one_sub hs.measurableSet] at hv
    change tvDist μ ν = (ν s).toReal - (μ s).toReal + _ at hv
    simp only [measureReal_def] at hv
    rw [← ENNReal.ofReal_toReal (measure_ne_top D univ)]
    exact congrArg ENNReal.ofReal (by linarith)

/-- Transfer a hard selection through a common submeasure, charging only the excess mass. -/
theorem transfer_hard {μ ν common D : Measure Gap} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hcommon : common ≤ μ) (hν : D + common = ν) (ρ B : ℝ) (S : Set Gap) (hs : MeasurableSet S) :
    selection ν ρ B ≤ selectionObjective μ ρ B (μ.restrict S) + D univ := by
  have : IsFiniteMeasure common := isFiniteMeasure_of_le μ hcommon
  have hsum : (D + common.restrict Sᶜ) + common.restrict S = ν := by
    rw [add_assoc, Measure.restrict_compl_add_restrict hs, hν]
  have hsub : common.restrict S ≤ ν := (show common.restrict S ≤ _ + common.restrict S from
    Measure.le_add_left le_rfl).trans_eq hsum
  have hres : ν - common.restrict S = D + common.restrict Sᶜ := by
    conv_lhs => lhs; rw [← hsum]
    exact Measure.add_sub_cancel
  have hresμ : μ - μ.restrict S = μ.restrict Sᶜ := by
    conv_lhs => lhs; rw [← Measure.restrict_compl_add_restrict hs (μ := μ)]
    exact Measure.add_sub_cancel
  have hg := gamma_mono (Measure.restrict_mono (s := S) Subset.rfl hcommon)
  have ht : tailCost (common.restrict Sᶜ) (1/sqrt B) ≤ tailCost (μ.restrict Sᶜ) (1/sqrt B) :=
    lintegral_mono' (Measure.restrict_mono Subset.rfl hcommon) le_rfl
  apply (selection_le_objective hsub ρ B).trans
  unfold selectionObjective
  rw [hres, hresμ]
  have ha (h : ℝ) : tailCost (D + common.restrict Sᶜ) h = tailCost D h + tailCost (common.restrict Sᶜ) h := by
    simp only [tailCost, lintegral_add_measure]
  rw [ha, add_comm (tailCost D _), ← add_assoc]
  apply add_le_add _ (tailCost_le_mass _ _)
  exact add_le_add (mul_le_mul_right (ENNReal.rpow_le_rpow
    (mul_le_mul_right hg _) (by norm_num)) _) ht

theorem selection_le_tv (μ ν : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ρ B : ℝ} (hρ : 0 < ρ) (hr : ρ ≤ 1/4) (hB : 0 < B) :
    selection ν ρ B ≤ selection μ ρ B + ENNReal.ofReal (tvDist μ ν / 2) := by
  obtain ⟨common,D,hcommon,hν,hm⟩ := common_part μ ν
  conv_rhs => rw [selection, hard_selection ρ B hρ hr hB μ, ← min_add_add_right, ENNReal.iInf₂_add]
  apply le_min ((selection_le_rho ν ρ B).trans le_self_add)
  exact le_iInf₂ fun S hs => hm ▸ transfer_hard hcommon hν ρ B S hs

theorem total_variation_stability : TVStatement := by
  intro μ ν _ _ ρ B hρ hr hB
  have hl (α β : Measure Gap) [IsProbabilityMeasure α] [IsProbabilityMeasure β] :
      (selection β ρ B).toReal ≤ (selection α ρ B).toReal + tvDist α β / 2 := by
    have hf := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (selection_le_rho α ρ B)
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf,ENNReal.ofReal_ne_top⟩)
      (selection_le_tv α β hρ hr hB)
    rwa [ENNReal.toReal_add hf ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (div_nonneg tvDist_nonneg (by norm_num))] at h
  have h₁ := hl μ ν
  have h₂ := hl ν μ
  rw [tvDist_comm ν μ] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end ThresholdHC.SelectionStability
