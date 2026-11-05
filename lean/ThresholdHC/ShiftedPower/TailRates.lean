import ThresholdHC.SubcriticalPower.Full
import ThresholdHC.Proofs.Modulus

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace ThresholdHC.ShiftedPower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile ThresholdHC.SubcriticalPower

def linearRate (ρ x : ℝ) := min ρ (x*(1+max 0 (Real.log (ρ/x))))

def intermediateRate (α ρ x : ℝ) := min ρ (ρ^(1-1/α)*x)

/-- At exponent one, clipping the CDF at rarity produces the logarithm of
the ratio of rarity to resolution. -/
theorem linear_tail (μ : Measure Gap) [IsProbabilityMeasure μ] {a ρ h : ℝ}
    (hm : ExactPowerLaw μ 1 a) (ha : 0 < a) (hr : 0 < ρ) (hu : ρ ≤ 1) (hh : 0 < h) :
    linearRate ρ (h/a) ≤ tailModulus (quantileTail μ ρ) h := by
  let x := h/a
  have hx : 0 < x := div_pos hh ha
  by_cases hs : ρ ≤ x
  · have h := power_tail_floor μ hm hr hu hh
    rw [Real.rpow_one,min_eq_left hs] at h
    exact (min_le_left _ _).trans h
  have hxr : x < ρ := lt_of_not_ge hs
  let u := x/ρ
  have hu0 : 0 < u := div_pos hx hr
  have hu1 : u < 1 := (div_lt_one hr).mpr hxr
  let _ := isFiniteMeasure_of_le μ (quantileTail_le μ hr hu)
  rw [tail_layers _ hh.le]
  have he : (∫ t in (0:ℝ)..1, (quantileTail μ ρ).real {d : Gap | (d:ℝ) ≤ h/t}) =
      ρ*(∫ t in (0:ℝ)..1, min 1 (u/t)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t ht
    rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    rw [quantile_cdf μ hr hu _,hm _ (div_pos hh ht.1),Real.rpow_one,← min_assoc,min_eq_left hu,
      mul_min_of_nonneg _ _ hr.le,mul_one]
    congr 1
    dsimp [u,x]; field_simp
  rw [he,ThresholdHC.Proofs.power_modulus_critical u hu0 hu1]
  apply (min_le_right _ _).trans_eq
  have hl : 0 ≤ Real.log (ρ/x) := Real.log_nonneg ((one_le_div hx).mpr hxr.le)
  change x*(1+max 0 (Real.log (ρ/x))) = ρ*(u*(1-Real.log u))
  rw [max_eq_right hl,show ρ/x = u⁻¹ by simp [u,inv_div],Real.log_inv]
  dsimp [u]; field_simp; ring

/-- On the lower-quantile region every gap is at most a times the
appropriate power of rarity. The bound is sharp for exponents above one. -/
theorem intermediate_tail (μ : Measure Gap) [IsProbabilityMeasure μ] {α a ρ h : ℝ}
    (hm : ExactPowerLaw μ α a) (hα : 0 < α) (ha : 0 < a)
    (hr : 0 < ρ) (hu : ρ ≤ 1) (hh : 0 < h) :
    intermediateRate α ρ (h/a) ≤ tailModulus (quantileTail μ ρ) h := by
  let t := a*ρ^(1/α)
  have ht : 0 < t := mul_pos ha (Real.rpow_pos_of_pos hr _)
  have hF : μ.real {d : Gap | (d:ℝ) ≤ t} = ρ := by
    rw [hm t ht,show t/a = ρ^(1/α) by dsimp [t]; field_simp,← Real.rpow_mul hr.le,
      one_div_mul_cancel hα.ne',Real.rpow_one,min_eq_right hu]
  have hcut : quantileThreshold μ ρ ≤ t := by
    by_contra! hlt
    exact ((quantileThreshold_properties μ hr hu).2.2.2 t hlt).ne hF
  let η := quantileTail μ ρ
  let _ : IsFiniteMeasure η := isFiniteMeasure_of_le μ (quantileTail_le μ hr hu)
  have hpoint : ∀ᵐ d : Gap ∂η, min 1 (h/t) ≤ min 1 (h/(d:ℝ)) := by
    filter_upwards [quantileTail_support μ ρ] with d hd
    exact min_le_min_left _ (div_le_div_of_nonneg_left hh.le d.property.1 (hd.trans hcut))
  have hi := integral_mono_ae (integrable_const (min 1 (h/t))) (tailKernel_integrable η hh.le) hpoint
  rw [integral_const,smul_eq_mul] at hi
  change η.real univ*min 1 (h/t) ≤ tailModulus η h at hi
  rw [quantileTail_real_mass μ hr hu,mul_min_of_nonneg _ _ hr.le,mul_one] at hi
  apply le_trans _ hi
  apply min_le_min_left
  rw [Real.rpow_sub hr,Real.rpow_one]
  dsimp [t]
  apply le_of_eq
  ring

end ThresholdHC.ShiftedPower
