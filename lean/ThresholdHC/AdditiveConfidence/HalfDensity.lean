import ThresholdHC.ConfidenceLocalization.ConfidenceRate

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace ThresholdHC.AdditiveConfidence
open ThresholdHC.Tier6

/-- A half-prior version of the density of the combined positive-sign measure. -/
def halfSign (μ σ : Measure Gap) : SignLaw :=
  ⟨fun d => min (1/2) (σ.rnDeriv μ d).toReal, by
    constructor
    · exact measurable_const.min ((Measure.measurable_rnDeriv _ _).ennreal_toReal)
    · intro d
      exact ⟨le_min (by norm_num) ENNReal.toReal_nonneg,(min_le_left _ _).trans (by norm_num)⟩⟩

theorem halfSign_le_half (μ σ : Measure Gap) (d : Gap) :
    (halfSign μ σ).val d ≤ 1/2 := min_le_left _ _

theorem measure_le_of_twice_le {X : Type} [MeasurableSpace X] (μ σ : Measure X)
    (h : (2 : ℝ≥0) • σ ≤ μ) : σ ≤ μ := by
  refine le_trans ?_ h
  apply Measure.le_iff'.mpr
  intro S
  rw [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul]
  calc
    σ S = 1*σ S := by rw [one_mul]
    _ ≤ _ := mul_le_mul' (by norm_num) le_rfl

theorem halfSign_density (μ σ : Measure Gap) [IsProbabilityMeasure μ] [IsFiniteMeasure σ]
    (h : (2 : ℝ≥0) • σ ≤ μ) :
    μ.withDensity (fun d => ENNReal.ofReal ((halfSign μ σ).val d)) = σ := by
  have hle := measure_le_of_twice_le μ σ h
  have he : (fun d => ENNReal.ofReal ((halfSign μ σ).val d)) =ᵐ[μ] σ.rnDeriv μ := by
    filter_upwards [Measure.rnDeriv_le_one_of_le h,Measure.rnDeriv_smul_left σ μ (2 : ℝ≥0),
      Measure.rnDeriv_ne_top σ μ] with d hd hs ht
    have hr := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) hd
    rw [hs] at hr
    simp only [Pi.smul_apply,ENNReal.smul_def,smul_eq_mul,ENNReal.toReal_mul,
      ENNReal.coe_toReal,NNReal.coe_ofNat,ENNReal.toReal_one] at hr
    have hh : (σ.rnDeriv μ d).toReal ≤ 1/2 := by linarith
    change ENNReal.ofReal (min (1/2) (σ.rnDeriv μ d).toReal) = _
    rw [min_eq_right hh,ENNReal.ofReal_toReal ht]
  rw [withDensity_congr_ae he]
  exact Measure.withDensity_rnDeriv_eq _ _ hle.absolutelyContinuous

theorem halfSign_integral (μ σ : Measure Gap) [IsProbabilityMeasure μ] [IsFiniteMeasure σ]
    (h : (2 : ℝ≥0) • σ ≤ μ) (F : Gap → ℝ) :
    (∫ d, (halfSign μ σ).val d*F d ∂μ) = ∫ d, F d ∂σ := by
  have hm : Measurable (fun d => ENNReal.ofReal ((halfSign μ σ).val d)) :=
    ENNReal.measurable_ofReal.comp (halfSign μ σ).property.1
  have he := integral_withDensity_eq_integral_toReal_smul (μ := μ) hm
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) F
  simp_rw [ENNReal.toReal_ofReal ((halfSign μ σ).property.2 _).1,smul_eq_mul] at he
  rw [halfSign_density μ σ h] at he
  exact he.symm

theorem halfSign_mean (μ σ : Measure Gap) [IsProbabilityMeasure μ] [IsFiniteMeasure σ]
    (h : (2 : ℝ≥0) • σ ≤ μ) :
    signMean μ (halfSign μ σ).val = σ.real Set.univ := by
  have he := halfSign_integral μ σ h (fun _ => 1)
  simpa [signMean] using he

end ThresholdHC.AdditiveConfidence
