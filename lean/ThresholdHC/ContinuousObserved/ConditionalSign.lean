import ThresholdHC.ContinuousObserved.Target

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved
open ThresholdHC.Tier6

def positiveGapLaw {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool) : Measure Gap :=
  (volume.restrict {u : unitInterval | s (D.cell u) = true}).map D.gap

instance positiveGapLaw_finite {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool) :
    IsFiniteMeasure (positiveGapLaw D s) := by
  unfold positiveGapLaw
  infer_instance

theorem positiveGapLaw_le {N : ℕ} (D : QueryDesign N) (s : Fin N → Bool)
    (μ : Measure Gap) (hl : volume.map D.gap = μ) : positiveGapLaw D s ≤ μ := by
  rw [← hl]
  exact Measure.map_mono Measure.restrict_le_self D.gap_measurable

/-- A measurable conditional sign probability obtained from the positive
gap submeasure. Its version takes values in the unit interval everywhere. -/
def conditionalSign {N : ℕ} (μ : Measure Gap) (D : QueryDesign N) (s : Fin N → Bool) : SignLaw :=
  ⟨fun d => min 1 ((positiveGapLaw D s).rnDeriv μ d).toReal, by
    constructor
    · exact measurable_const.min ((Measure.measurable_rnDeriv _ _).ennreal_toReal)
    · intro d
      exact ⟨le_min (by norm_num) ENNReal.toReal_nonneg,min_le_left _ _⟩⟩

theorem conditionalSign_density {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (D : QueryDesign N) (s : Fin N → Bool) (hl : volume.map D.gap = μ) :
    μ.withDensity (fun d => ENNReal.ofReal ((conditionalSign μ D s).val d)) = positiveGapLaw D s := by
  have hle := positiveGapLaw_le D s μ hl
  have he : (fun d => ENNReal.ofReal ((conditionalSign μ D s).val d)) =ᵐ[μ]
      (positiveGapLaw D s).rnDeriv μ := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hle] with d hd
    have hr : ((positiveGapLaw D s).rnDeriv μ d).toReal ≤ 1 := by
      simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) hd
    change ENNReal.ofReal (min 1 ((positiveGapLaw D s).rnDeriv μ d).toReal) = _
    rw [min_eq_right hr,ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by simp) hd)]
  rw [withDensity_congr_ae he]
  exact Measure.withDensity_rnDeriv_eq _ _ hle.absolutelyContinuous

theorem conditionalSign_positive_integral {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (D : QueryDesign N) (s : Fin N → Bool) (hl : volume.map D.gap = μ)
    (F : Gap → ℝ) (hF : Measurable F) :
    (∫ d, (conditionalSign μ D s).val d * F d ∂μ) =
      ∫ u in {u : unitInterval | s (D.cell u) = true}, F (D.gap u) := by
  have hm : Measurable (fun d => ENNReal.ofReal ((conditionalSign μ D s).val d)) :=
    ENNReal.measurable_ofReal.comp (conditionalSign μ D s).property.1
  have he := integral_withDensity_eq_integral_toReal_smul (μ := μ) hm
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) F
  simp_rw [ENNReal.toReal_ofReal ((conditionalSign μ D s).property.2 _).1,smul_eq_mul] at he
  rw [conditionalSign_density μ D s hl] at he
  rw [← he,positiveGapLaw,integral_map D.gap_measurable.aemeasurable hF.aestronglyMeasurable]

end ThresholdHC.ContinuousObserved
