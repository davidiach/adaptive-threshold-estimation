import ThresholdHC.ContinuousObserved.Cutoff
import ThresholdHC.SmoothDensity.Envelope

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved
open ThresholdHC.Tier6 ThresholdHC.ObservedState ThresholdHC.RareAboveTwo

def quarterGap : Gap := ⟨1 / 4,by norm_num⟩

def uniformGaps : Measure Gap := powerGapLaw 1 (1 / 4) (by norm_num) (by norm_num) (by norm_num)

instance uniformGaps_probability : IsProbabilityMeasure uniformGaps := by
  unfold uniformGaps
  infer_instance

theorem uniformGaps_cdf {x : ℝ} (hx : 0 < x) :
    uniformGaps.real {d : Gap | (d : ℝ) ≤ x} = min 1 (4 * x) := by
  rw [uniformGaps,powerGapLaw_cdf _ _ _ _ _ _ hx,Real.rpow_one]
  congr 1
  ring

theorem uniformGaps_support : ∀ᵐ d ∂uniformGaps, d ≤ quarterGap := by
  have hp (u : ℝ) :
      powerQuantile 1 (1 / 4) (by norm_num) (by norm_num) (by norm_num) u ≤ quarterGap := by
    by_cases hu : 0 < u ∧ u ≤ 1
    · change (powerQuantile 1 (1 / 4) (by norm_num) (by norm_num) (by norm_num) u : ℝ) ≤ 1 / 4
      simp only [powerQuantile,dite_eq_left hu,inv_one,Real.rpow_one]
      nlinarith [hu.2]
    · simp [powerQuantile,hu,quarterGap]
  change ∀ᵐ d ∂(ThresholdHC.CriticalEntropy.uniformUnitMeasure.map
    (powerQuantile 1 (1 / 4) (by norm_num) (by norm_num) (by norm_num))), d ≤ quarterGap
  apply (ae_map_iff (measurable_powerQuantile _ _ _ _ _).aemeasurable
    (measurableSet_le measurable_subtype_coe measurable_const)).mpr
  exact ae_of_all _ hp

theorem uniformGaps_modulus {h : ℝ} (hh : 0 < h) (ha : h < 1 / 4) :
    modulus uniformGaps h = 4 * h * (1 + Real.log (1 / (4 * h))) := by
  rw [uniformGaps,ThresholdHC.SmoothDensity.linear_modulus (1 / 4) h (by norm_num) (by norm_num) hh ha]
  congr 2
  · ring
  · congr 1
    ring

theorem uniform_design_exists (h : Gap) {δ : ℝ} (hδ : 0 < δ) :
    ∃ D : CellDesign uniformGaps h δ,
      (∀ u, (D.gap u : ℝ) ≤ 1 / 4) ∧ (∀ i, (D.cap i : ℝ) ≤ 1 / 4) := by
  obtain ⟨D⟩ := cell_design_exists uniformGaps h hδ
  let E := cappedDesign uniformGaps quarterGap h hδ.le uniformGaps_support D
  refine ⟨E,?_,?_⟩
  · intro u
    exact capGap_le quarterGap (D.gap u)
  · intro i
    exact capGap_le quarterGap (D.cap i)

end ThresholdHC.ContinuousObserved
