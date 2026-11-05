
import ThresholdHC.AnytimeLower.TailProfiles
import ThresholdHC.EntropyTail.Objective
import ThresholdHC.QuantileSelection.Full

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile

theorem profileMass_eq_restricted_tail (μ : Measure Gap) (τ h : ℝ) :
    profileMass μ τ h = tailModulus (μ.restrict {d : Gap | (d:ℝ) ≤ τ}) h := by
  unfold profileMass tailModulus
  change (∫ d, ({d : Gap | (d:ℝ) ≤ τ}).indicator (fun d => min 1 (h/(d:ℝ))) d ∂μ) = _
  exact integral_indicator (measurableSet_le measurable_subtype_coe measurable_const)

theorem tailModulus_le_profile_add (μ : Measure Gap) [IsProbabilityMeasure μ]
    {τ h : ℝ} (hτ : 0 < τ) (hh : 0 ≤ h) :
    tailModulus μ h ≤ profileMass μ τ h+h/τ := by
  have hsum : Integrable (fun d => tailProfile τ h d+h/τ) μ :=
    (integrable_tailProfile μ τ hh).add (integrable_const (h/τ))
  have hi := integral_mono (tailKernel_integrable μ hh) hsum (fun d => by
      by_cases hd : (d:ℝ) ≤ τ
      · simp only [tailProfile,ite_eq_left hd]
        exact le_add_of_nonneg_right (div_nonneg hh hτ.le)
      · simp only [tailProfile,ite_eq_right hd,zero_add]
        exact (min_le_right _ _).trans (div_le_div_of_nonneg_left hh hτ (not_le.mp hd).le))
  rw [integral_add (integrable_tailProfile μ τ hh) (integrable_const (h/τ))] at hi
  simpa only [tailModulus,profileMass,integral_const,probReal_univ,one_smul] using hi

theorem selection_le_profile_add (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ThresholdHC.EntropyTail.selection μ ρ B ≤
      ENNReal.ofReal (profileMass μ τ (ThresholdHC.EntropyTailQuantile.budgetScale B)+ThresholdHC.EntropyTailQuantile.budgetScale B/τ) := by
  have he := ThresholdHC.EntropyTail.selection_le_objective (Measure.zero_le μ) ρ B
  rw [ThresholdHC.EntropyTail.selectionObjective_zero,one_div,
    ← ThresholdHC.EntropyTail.quantile_tailModulus_eq μ (inv_nonneg.mpr (sqrt_nonneg B))] at he
  exact he.trans (ENNReal.ofReal_le_ofReal (tailModulus_le_profile_add μ hτ (ThresholdHC.EntropyTailQuantile.budgetScale_nonneg B)))

theorem profile_le_selection (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ τ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hm : μ.real {d : Gap | (d:ℝ) ≤ τ} < ρ) (B : ℝ) :
    ENNReal.ofReal (profileMass μ τ (ThresholdHC.EntropyTailQuantile.budgetScale B)) ≤ ThresholdHC.EntropyTail.selection μ ρ B := by
  have hτ : τ < quantileThreshold μ ρ := by
    by_contra hh
    have hle : quantileThreshold μ ρ ≤ τ := not_lt.mp hh
    have hmeasure : μ.real {d : Gap | (d:ℝ) ≤ quantileThreshold μ ρ} ≤
        μ.real {d : Gap | (d:ℝ) ≤ τ} :=
      measureReal_mono (fun d hd => hd.trans hle) (measure_ne_top μ _)
    exact (not_le.mpr hm) ((quantileThreshold_properties μ hρ hρ1).2.2.1.trans hmeasure)
  have hsub : μ.restrict {d : Gap | (d:ℝ) ≤ τ} ≤ quantileTail μ ρ := by
    have hi : μ.restrict {d : Gap | (d:ℝ) ≤ τ} ≤
        μ.restrict {d : Gap | (d:ℝ) < quantileThreshold μ ρ} :=
      Measure.restrict_mono_set μ (fun d hd => (show (d:ℝ) ≤ τ from hd).trans_lt hτ)
    exact hi.trans (le_add_of_nonneg_right bot_le)
  let : IsFiniteMeasure (quantileTail μ ρ) :=
    isFiniteMeasure_of_le μ (quantileTail_le μ hρ hρ1)
  rw [profileMass_eq_restricted_tail]
  exact (ENNReal.ofReal_le_ofReal (tailModulus_mono hsub (ThresholdHC.EntropyTailQuantile.budgetScale_nonneg B))).trans
    ((quantileTail_le_selectionValue μ hρ hρ1 B).trans
      (ThresholdHC.EntropyTail.quantile_selectionValue_le μ ρ B))

end ThresholdHC.AnytimeLower
