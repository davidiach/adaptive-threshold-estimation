import ThresholdHC.SmoothDensity.Separation
import ThresholdHC.Tier6.AlgorithmModel

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.SmoothDensity
open ThresholdHC.Tier6

def gapVolume : Measure Gap := Measure.comap (Subtype.val : Gap → ℝ) volume

def smoothGapLaw : Measure Gap :=
  gapVolume.withDensity (fun d => ENNReal.ofReal (2 * baseDensity d))

theorem positive_integral_eq (F : ℝ → ℝ) :
    (∫ x in Ioc (0 : ℝ) (1 / 2), baseDensity x * F x) =
      ∫ x in Ioi (0 : ℝ), baseDensity x * F x := by
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (s := Ioc (0 : ℝ) (1 / 2)) (fun _ hx => hx.1)
  intro x hx
  have hx' : 1 / 2 < x := by
    by_contra h
    exact hx.2 ⟨hx.1, le_of_not_gt h⟩
  rw [baseDensity_zero (by linarith [le_abs_self x]), zero_mul]

theorem baseDensity_half : 2 * (∫ x in Ioi (0 : ℝ), baseDensity x) = 1 := by
  have he : (fun x => baseDensity |x|) = baseDensity := by
    funext x
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, baseDensity_even]
  have hi := integral_comp_abs (f := baseDensity)
  rw [he, baseDensity_integral] at hi
  exact hi.symm

theorem smoothGapLaw_integral (F : ℝ → ℝ) :
    (∫ d, F (d : ℝ) ∂smoothGapLaw) =
      2 * ∫ x in Ioi (0 : ℝ), baseDensity x * F x := by
  have hm : Measurable (fun d : Gap => ENNReal.ofReal (2 * baseDensity d)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (baseDensity_contDiff.continuous.measurable.comp measurable_subtype_coe))
  unfold smoothGapLaw
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have ht (d : Gap) : (ENNReal.ofReal (2 * baseDensity d)).toReal = 2 * baseDensity d :=
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (baseDensity_nonneg d))
  simp_rw [ht, smul_eq_mul]
  change (∫ d : Ioc (0 : ℝ) (1 / 2), 2 * baseDensity d * F d
    ∂Measure.comap Subtype.val volume) = _
  rw [integral_subtype_comap measurableSet_Ioc (fun x : ℝ => 2 * baseDensity x * F x)]
  simp_rw [mul_assoc]
  rw [integral_const_mul, positive_integral_eq]

instance smoothGapLaw_probability : IsProbabilityMeasure smoothGapLaw where
  measure_univ := by
    rw [smoothGapLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    change (∫⁻ d : Ioc (0 : ℝ) (1 / 2), ENNReal.ofReal (2 * baseDensity d)
      ∂Measure.comap Subtype.val volume) = 1
    rw [lintegral_subtype_comap measurableSet_Ioc (fun x : ℝ => ENNReal.ofReal (2 * baseDensity x)),
      ← ofReal_integral_eq_lintegral_ofReal (baseDensity_integrable.const_mul 2).integrableOn
        (ae_of_all _ (fun x => mul_nonneg (by norm_num) (baseDensity_nonneg x)))]
    have he := positive_integral_eq (fun _ => (1 : ℝ))
    simp only [mul_one] at he
    rw [integral_const_mul, he, baseDensity_half]
    norm_num

def smoothSign (s : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (plus : Bool) : SignLaw :=
  ⟨fun d => 1 / 2 + (if plus then 1 else -1) * perturbation s t d,
    measurable_const.add (measurable_const.mul
      ((perturbation_contDiff s t).continuous.measurable.comp measurable_subtype_coe)),
    fun d => by
      have hb := perturbation_abs_le s ht.le ht1 d
      have hl := neg_le_abs (perturbation s t d)
      have hu := le_abs_self (perturbation s t d)
      cases plus <;> norm_num <;> constructor <;> linarith⟩

theorem smoothSign_separation (s : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 64) :
    t ^ (s + 1) / 8 * Real.log (1 / t) ≤
      signMean smoothGapLaw (smoothSign s ht (by linarith) true).val -
        signMean smoothGapLaw (smoothSign s ht (by linarith) false).val := by
  unfold signMean smoothSign
  simp only [ite_true, Bool.false_eq_true, ite_false, one_mul, neg_one_mul]
  rw [smoothGapLaw_integral (fun x => 1 / 2 + perturbation s t x),
    smoothGapLaw_integral (fun x => 1 / 2 + -perturbation s t x)]
  have h := centered_pair_separation s ht ht1
  have hi := perturbation_integrable s t
  simp only [centeredDensity,
    integral_add baseDensity_integrable.integrableOn (hi.const_mul _).integrableOn,
    integral_const_mul] at h
  have hePlus : (fun x => baseDensity x * (1 / 2 + perturbation s t x)) =
      (fun x => baseDensity x / 2 + baseDensity x * perturbation s t x) := by funext x; ring
  have heMinus : (fun x => baseDensity x * (1 / 2 + -perturbation s t x)) =
      (fun x => baseDensity x / 2 - baseDensity x * perturbation s t x) := by funext x; ring
  rw [hePlus, heMinus, integral_add (baseDensity_integrable.div_const 2).integrableOn hi.integrableOn,
    integral_sub (baseDensity_integrable.div_const 2).integrableOn hi.integrableOn]
  linarith

end ThresholdHC.SmoothDensity
