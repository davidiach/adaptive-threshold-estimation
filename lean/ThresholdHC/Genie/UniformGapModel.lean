import ThresholdHC.Genie.RevealFiniteness
import ThresholdHC.StoppingProgram.PositiveValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The uniform positive-gap law and the explicit priors used for the
infinite-latent-divergence counterexample. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram
open ThresholdHC.CapIdentification

def uniformGapLaw : Measure Gap :=
  (2 : ℝ≥0∞) • Measure.comap (Subtype.val : Gap → ℝ) volume

instance uniformGapLaw_probability : IsProbabilityMeasure uniformGapLaw where
  measure_univ := by
    unfold uniformGapLaw
    rw [Measure.smul_apply]
    change 2*(Measure.comap (Subtype.val : Set.Ioc (0:ℝ) (1/2) → ℝ) volume) Set.univ = 1
    rw [comap_subtype_coe_apply measurableSet_Ioc]
    simp only [Set.image_univ,Subtype.range_coe]
    change 2*volume (Set.Ioc (0:ℝ) (1/2)) = 1
    rw [Real.volume_Ioc]
    norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

theorem uniformGap_integral (f : ℝ → ℝ) :
    (∫ d : Gap, f d.val ∂uniformGapLaw) = 2*(∫ x in (0:ℝ)..(1/2), f x) := by
  rw [uniformGapLaw,integral_smul_measure]
  change ENNReal.toReal 2 • (∫ x : Set.Ioc (0:ℝ) (1/2), f x.val ∂Measure.comap Subtype.val volume) = _
  rw [integral_subtype_comap measurableSet_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1/2)]
  norm_num

def singularVariancePrior : SignLaw :=
  ⟨fun d => 1/2-d.val,measurable_const.sub measurable_subtype_coe,
    fun d => ⟨by linarith [d.property.2],by linarith [d.property.1]⟩⟩

def singularExamplePriors : FourPriors :=
  ⟨nullSignLaw,constantPrior (1/4) (by norm_num),singularVariancePrior,
    constantPrior (1/4) (by norm_num)⟩

theorem singularVariancePrior_mean : signMean uniformGapLaw singularVariancePrior.val = 1/4 := by
  change (∫ d : Gap, (1/2:ℝ)-d.val ∂uniformGapLaw) = _
  rw [uniformGap_integral]
  have hc : IntervalIntegrable (fun _ : ℝ => (1/2:ℝ)) volume 0 (1/2) := intervalIntegrable_const
  have hi : IntervalIntegrable (fun x : ℝ => x) volume 0 (1/2) := continuous_id.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hc hi,
    intervalIntegral.integral_const,integral_id]
  norm_num

theorem singularExample_admissible : Admissible uniformGapLaw (1/4) singularExamplePriors := by
  refine ⟨?_,?_,?_,?_⟩
  · simp [RarePrior,signMean,singularExamplePriors,nullSignLaw]
  · exact le_of_eq (constantPrior_mean uniformGapLaw (1/4) (by norm_num))
  · exact le_of_eq singularVariancePrior_mean
  · exact le_of_eq (constantPrior_mean uniformGapLaw (1/4) (by norm_num))

end ThresholdHC.Genie
