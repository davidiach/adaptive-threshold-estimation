import ThresholdHC.RareAboveTwo.Specification
import ThresholdHC.CriticalEntropy.PopulationModel
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! An explicit nonempty family of exact power laws, with the prescribed
positive support. The auxiliary uniform variable is used only to define the
gap law, and is not exposed to any estimator. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy

def powerQuantile (α a : ℝ) (hα : 0 < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (u : ℝ) : Gap :=
  if hu : 0 < u ∧ u ≤ 1 then
    ⟨a*u^(α⁻¹), mul_pos ha (Real.rpow_pos_of_pos hu.1 _),
      (mul_le_of_le_one_right ha.le (Real.rpow_le_one hu.1.le hu.2 (inv_pos.mpr hα).le)).trans ha'⟩
  else ⟨a,ha,ha'⟩

theorem measurable_powerQuantile (α a : ℝ) (hα : 0 < α) (ha : 0 < a) (ha' : a ≤ 1/2) :
    Measurable (powerQuantile α a hα ha ha') := by
  apply Measurable.subtype_mk
  have he : (fun u => (powerQuantile α a hα ha ha' u : ℝ)) =
      (fun u : ℝ => if 0 < u ∧ u ≤ 1 then a*u^(α⁻¹) else a) := by
    funext u
    by_cases hu : 0 < u ∧ u ≤ 1 <;> simp [powerQuantile,hu]
  change Measurable (fun u => (powerQuantile α a hα ha ha' u : ℝ))
  rw [he]
  exact Measurable.ite measurableSet_Ioc (by fun_prop) measurable_const

def powerGapLaw (α a : ℝ) (hα : 0 < α) (ha : 0 < a) (ha' : a ≤ 1/2) : Measure Gap :=
  uniformUnitMeasure.map (powerQuantile α a hα ha ha')

instance powerGapLaw_probability (α a : ℝ) (hα : 0 < α) (ha : 0 < a) (ha' : a ≤ 1/2) :
    IsProbabilityMeasure (powerGapLaw α a hα ha ha') :=
  by unfold powerGapLaw; infer_instance

theorem uniformUnit_ae_positive : ∀ᵐ u ∂uniformUnitMeasure, 0 < u ∧ u ≤ 1 := by
  have hzero : ∀ᵐ u ∂uniformUnitMeasure, u ≠ 0 := by
    rw [ae_iff]
    simp [uniformUnitMeasure]
  filter_upwards [ae_restrict_mem measurableSet_Icc,hzero] with u hu hne
  exact ⟨lt_of_le_of_ne hu.1 (Ne.symm hne),hu.2⟩

theorem powerQuantile_le_iff (α a : ℝ) (hα : 0 < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (u x : ℝ) (hu : 0 < u ∧ u ≤ 1) (hx : 0 < x) :
    (powerQuantile α a hα ha ha' u : ℝ) ≤ x ↔ u ≤ (x/a)^α := by
  simp only [powerQuantile,dite_eq_left hu]
  rw [← le_div_iff₀' ha]
  have h := Real.rpow_le_rpow_iff (Real.rpow_nonneg hu.1.le (α⁻¹))
    (div_pos hx ha).le hα
  simpa only [Real.rpow_inv_rpow hu.1.le hα.ne'] using h.symm

theorem powerGapLaw_cdf (α a : ℝ) (hα : 0 < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (x : ℝ) (hx : 0 < x) :
    (powerGapLaw α a hα ha ha').real {d | (d : ℝ) ≤ x} = min 1 ((x/a)^α) := by
  have hp : 0 < (x/a)^α := Real.rpow_pos_of_pos (div_pos hx ha) α
  have ht : 0 < min 1 ((x/a)^α) := lt_min (by norm_num) hp
  have hm : MeasurableSet {d : Gap | (d : ℝ) ≤ x} :=
    measurableSet_le measurable_subtype_coe measurable_const
  rw [measureReal_def,powerGapLaw,Measure.map_apply (measurable_powerQuantile α a hα ha ha') hm]
  have he : (powerQuantile α a hα ha ha') ⁻¹' {d : Gap | (d : ℝ) ≤ x} =ᵐ[uniformUnitMeasure]
      Ioc 0 (min 1 ((x/a)^α)) := by
    filter_upwards [uniformUnit_ae_positive] with u hu
    simp only [mem_preimage,mem_ofPred_eq,powerQuantile_le_iff α a hα ha ha' u x hu hx,
      mem_Ioc,le_min_iff]
    simp [hu.1,hu.2]
  rw [measure_congr he,uniformUnitMeasure,Measure.restrict_apply measurableSet_Ioc]
  have hi : Ioc 0 (min 1 ((x/a)^α)) ∩ Icc (0 : ℝ) 1 = Ioc 0 (min 1 ((x/a)^α)) := by
    apply inter_eq_left.mpr
    intro u hu
    exact ⟨hu.1.le,hu.2.trans (min_le_left _ _)⟩
  rw [hi,Real.volume_Ioc,sub_zero,ENNReal.toReal_ofReal ht.le]

theorem power_law_exists : PowerLawExistenceStatement := by
  intro α a hα ha ha'
  exact ⟨powerGapLaw α a hα ha ha',inferInstance,powerGapLaw_cdf α a hα ha ha'⟩

end ThresholdHC.RareAboveTwo
