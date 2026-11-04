import ThresholdHC.SelectionStability.MapCosts

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace ThresholdHC.SelectionStability
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

/-- Pushing a candidate forward commutes with removing its mass. -/
theorem map_objective (μ σ : Measure Gap) [IsFiniteMeasure μ] (hσ : σ ≤ μ) (T : Gap → Gap)
    (hm : Measurable T) (ρ B : ℝ) {r : ℝ} (hr : 1 ≤ r)
    (hd : ∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ))
    (hb : ∀ j, T ⁻¹' band j = band j) :
    selectionObjective (μ.map T) ρ B (σ.map T) ≤ selectionObjective μ ρ B σ ∧
    selectionObjective μ ρ B σ ≤ ENNReal.ofReal r * selectionObjective (μ.map T) ρ B (σ.map T) := by
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le μ hσ
  have hres : μ.map T - σ.map T = (μ-σ).map T := by
    have h := congrArg (fun ξ : Measure Gap => ξ.map T) (Measure.sub_add_cancel_of_le hσ)
    rw [Measure.map_add _ _ hm] at h
    rw [← h, Measure.add_sub_cancel]
  let h := 1 / sqrt B
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hc := (map_costs σ T hm hr hh hd hb).1
  have ht := (map_costs (μ-σ) T hm hr hh hd hb).2
  have hmono : gamma (σ.map T) ≤ gamma σ := by
    have H := gamma_le_scaled (σ := σ.map T) (τ := σ) (a := 1) (by norm_num)
      (fun j => by simpa using (hc j).1)
    simpa using H
  have hscale := gamma_le_scaled (sq_nonneg r) (fun j => (hc j).2)
  have hr₀ : 0 ≤ r := zero_le_one.trans hr
  have root : (ENNReal.ofReal (r^2)) ^ (1/2 : ℝ) = ENNReal.ofReal r := by
    rw [ENNReal.ofReal_pow hr₀, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  unfold selectionObjective
  rw [hres]
  constructor
  · exact add_le_add (mul_le_mul_right (ENNReal.rpow_le_rpow (mul_le_mul_right hmono _)
      (by norm_num)) _) ht.1
  · rw [mul_add]
    apply add_le_add _ ht.2
    calc
      _ ≤ ENNReal.ofReal h * (ENNReal.ofReal ρ * (ENNReal.ofReal (r^2) * gamma (σ.map T)))^(1/2 : ℝ) :=
        mul_le_mul_right (ENNReal.rpow_le_rpow (mul_le_mul_right hscale _) (by norm_num)) _
      _ = _ := by rw [mul_left_comm (ENNReal.ofReal ρ),
                    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),root]; ac_rfl

/-- The reverse bound lifts each hard set by preimage; injectivity is unnecessary. -/
theorem band_preserving_rounding : RoundingStatement := by
  intro μ _ T hm r ρ B hr hρ hrho hB hd hb
  have : IsProbabilityMeasure (μ.map T) := (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  have hrE : (1:ℝ≥0∞) ≤ ENNReal.ofReal r := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr
  have hne := ne_of_gt (lt_of_lt_of_le zero_lt_one hrE)
  constructor
  · change selection (μ.map T) ρ B ≤ min _ _
    refine le_min (selection_le_rho _ _ _) (le_iInf₂ fun σ hσ => ?_)
    exact (selection_le_objective (Measure.map_mono hσ hm) ρ B).trans
      (map_objective μ σ hσ T hm ρ B hr hd hb).1
  · conv_rhs => rw [selection, hard_selection ρ B hρ hrho hB (μ.map T), mul_min]
    apply le_min
    · exact (selection_le_rho μ ρ B).trans (by simpa only [one_mul] using mul_le_mul_left hrE (ENNReal.ofReal ρ))
    · rw [ENNReal.mul_iInf_of_ne hne ENNReal.ofReal_ne_top]
      refine le_iInf fun S => ?_
      rw [ENNReal.mul_iInf_of_ne hne ENNReal.ofReal_ne_top]
      refine le_iInf fun hs => ?_
      rw [Measure.restrict_map hm hs]
      exact (selection_le_objective Measure.restrict_le_self ρ B).trans
        (map_objective μ (μ.restrict (T ⁻¹' S)) Measure.restrict_le_self T hm ρ B hr hd hb).2

end ThresholdHC.SelectionStability
