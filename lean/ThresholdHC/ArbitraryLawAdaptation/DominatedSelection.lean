import ThresholdHC.ArbitraryLawAdaptation.ZeroAlgebra

/-! Restrict fractional selections with a bounded Radon--Nikodym density. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawAdaptation

theorem withDensity_base_mono {E : Type*} [MeasurableSpace E]
    {μ ν : Measure E} (h : μ ≤ ν) (w : E → ℝ≥0∞) :
    μ.withDensity w ≤ ν.withDensity w := by
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [withDensity_apply _ hs, withDensity_apply _ hs]
  exact lintegral_mono' (Measure.restrict_mono le_rfl h) le_rfl

def dominatedDensity (ζ ν : Measure ℝ) (x : ℝ) : ℝ≥0∞ := min 1 (ζ.rnDeriv ν x)

def dominatedSelection (ζ ν σ : Measure ℝ) : Measure ℝ :=
  σ.withDensity (dominatedDensity ζ ν)

theorem dominatedDensity_le_one (ζ ν : Measure ℝ) (x : ℝ) :
    dominatedDensity ζ ν x ≤ 1 := min_le_left _ _

theorem dominatedDensity_recovers {ζ ν : Measure ℝ} [IsFiniteMeasure ν] (h : ζ ≤ ν) :
    ν.withDensity (dominatedDensity ζ ν) = ζ := by
  have : IsFiniteMeasure ζ := isFiniteMeasure_of_le ν h
  calc
    _ = ν.withDensity (ζ.rnDeriv ν) := withDensity_congr_ae (by
      filter_upwards [Measure.rnDeriv_le_one_of_le h] with x hx
      exact min_eq_right hx)
    _ = ζ := Measure.withDensity_rnDeriv_eq _ _ (Measure.absolutelyContinuous_of_le h)

theorem dominatedSelection_le (ζ ν σ : Measure ℝ) : dominatedSelection ζ ν σ ≤ σ := by
  exact (withDensity_mono (Filter.Eventually.of_forall
    (dominatedDensity_le_one ζ ν))).trans_eq withDensity_one

theorem dominatedSelection_le_law {ζ ν σ : Measure ℝ} [IsFiniteMeasure ν]
    (h : ζ ≤ ν) (hσ : σ ≤ ν) : dominatedSelection ζ ν σ ≤ ζ := by
  exact (withDensity_base_mono hσ _).trans_eq (dominatedDensity_recovers h)

theorem dominatedSelection_residual {ζ ν σ : Measure ℝ} [IsFiniteMeasure ν]
    (h : ζ ≤ ν) (hσ : σ ≤ ν) :
    ζ-dominatedSelection ζ ν σ = (ν-σ).withDensity (dominatedDensity ζ ν) := by
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le ν hσ
  have : IsFiniteMeasure (dominatedSelection ζ ν σ) :=
    isFiniteMeasure_of_le σ (dominatedSelection_le ζ ν σ)
  have he : (ν-σ).withDensity (dominatedDensity ζ ν)+dominatedSelection ζ ν σ = ζ := by
    rw [dominatedSelection, ← withDensity_add_measure, Measure.sub_add_cancel_of_le hσ,
      dominatedDensity_recovers h]
  calc
    _ = ((ν-σ).withDensity (dominatedDensity ζ ν)+dominatedSelection ζ ν σ)-
        dominatedSelection ζ ν σ := congrArg (fun μ => μ-dominatedSelection ζ ν σ) he.symm
    _ = _ := Measure.add_sub_cancel

theorem dominatedSelection_residual_le {ζ ν σ : Measure ℝ} [IsFiniteMeasure ν]
    (h : ζ ≤ ν) (hσ : σ ≤ ν) : ζ-dominatedSelection ζ ν σ ≤ ν-σ := by
  rw [dominatedSelection_residual h hσ]
  exact (withDensity_mono (Filter.Eventually.of_forall
    (dominatedDensity_le_one ζ ν))).trans_eq withDensity_one

theorem dominatedSelection_objective {ζ ν σ : Measure ℝ} [IsFiniteMeasure ν]
    (h : ζ ≤ ν) (hσ : σ ≤ ν) (ρ B : ℝ) :
    zeroObjective ζ ρ B (dominatedSelection ζ ν σ) ≤ zeroObjective ν ρ B σ := by
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le ν hσ
  apply add_le_add
  · exact mul_le_mul_right (ENNReal.rpow_le_rpow
      (mul_le_mul_right (zeroGamma_mono (dominatedSelection_le ζ ν σ)) _) (by norm_num)) _
  · exact zeroTailCost_mono (dominatedSelection_residual_le h hσ) _

theorem zeroSelection_mono {ζ ν : Measure ℝ} [IsFiniteMeasure ν] (h : ζ ≤ ν) (ρ B : ℝ) :
    zeroSelection ζ ρ B ≤ zeroSelection ν ρ B := by
  apply le_min (min_le_left _ _)
  refine le_iInf fun σ => le_iInf fun hσ => ?_
  have hs := dominatedSelection_le_law h hσ
  have hle : zeroSelection ζ ρ B ≤ zeroObjective ζ ρ B (dominatedSelection ζ ν σ) :=
    (min_le_right _ _).trans (iInf₂_le (dominatedSelection ζ ν σ) hs)
  exact hle.trans (dominatedSelection_objective h hσ ρ B)

end ThresholdHC.ArbitraryLawAdaptation
