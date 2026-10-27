import ThresholdHC.CriticalEntropy.CriticalModel
import ThresholdHC.CriticalEntropy.EarlyDecision

/-! Normalization, exact interval masses and separated annuli of the quadratic law. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

instance criticalGapLaw_noAtoms : NullSingletonClass criticalGapLaw := by
  unfold criticalGapLaw
  infer_instance

theorem linear_density_interval (x y : ℝ) (hxy : x ≤ y) (hx : 0 ≤ x) :
    (∫⁻ d in Ioc x y, ENNReal.ofReal (32*d)) = ENNReal.ofReal (16*(y^2-x^2)) := by
  have hi : IntegrableOn (fun d : ℝ => 32*d) (Ioc x y) volume :=
    ((continuous_const.mul continuous_id).intervalIntegrable x y).1
  have hn : 0 ≤ᵐ[volume.restrict (Ioc x y)] (fun d : ℝ => 32*d) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with d hd
    have hd₀ : 0 ≤ d := hx.trans hd.1.le
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
    ← intervalIntegral.integral_of_le hxy,intervalIntegral.integral_const_mul,integral_id]
  congr 1
  ring

theorem criticalGapLaw_Ioc (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1/4) :
    criticalGapLaw (Ioc x y) = ENNReal.ofReal (16*(y^2-x^2)) := by
  rw [criticalGapLaw,withDensity_apply _ measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc]
  have he : Ioc x y ∩ Ioc (0 : ℝ) (1/4) = Ioc x y := by
    apply inter_eq_left.mpr
    intro d hd
    exact ⟨lt_of_le_of_lt hx hd.1,hd.2.trans hy⟩
  rw [he]
  exact linear_density_interval x y hxy hx

theorem criticalGapLaw_supported : criticalGapLaw (Ioc (0 : ℝ) (1/4))ᶜ = 0 := by
  apply withDensity_absolutelyContinuous
  simp

instance criticalGapLaw_probability : IsProbabilityMeasure criticalGapLaw where
  measure_univ := by
    have h := criticalGapLaw_Ioc 0 (1/4) (by norm_num) (by norm_num) le_rfl
    norm_num at h
    rw [← measure_add_measure_compl measurableSet_Ioc,criticalGapLaw_supported,h]
    simp

theorem criticalGapLaw_real_Ioc (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1/4) :
    criticalGapLaw.real (Ioc x y) = 16*(y^2-x^2) := by
  rw [measureReal_def,criticalGapLaw_Ioc x y hx hxy hy,ENNReal.toReal_ofReal]
  nlinarith

theorem criticalUpper_pos (j : ℕ) : 0 < criticalUpper j := by
  unfold criticalUpper
  positivity

theorem criticalUpper_le_quarter (j : ℕ) : criticalUpper j ≤ 1/4 := by
  have hpow : (1 : ℝ) ≤ 4^j := one_le_pow₀ (by norm_num)
  unfold criticalUpper
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 4) j)).mpr
  nlinarith

theorem criticalUpper_succ (j : ℕ) : criticalUpper (j+1) = criticalUpper j/4 := by
  simp only [criticalUpper,pow_succ]
  field_simp

theorem criticalAnnulus_mass (j : ℕ) :
    criticalGapLaw.real (criticalAnnulus j) = 3/(4*(16 : ℝ)^j) := by
  rw [criticalAnnulus,criticalGapLaw_real_Ioc _ _ (by positivity [criticalUpper_pos j])
    (by linarith [criticalUpper_pos j]) (criticalUpper_le_quarter j)]
  have hpow : (16 : ℝ)^j = ((4 : ℝ)^j)^2 := by
    simp only [pow_two,← mul_pow]
    norm_num
  rw [hpow]
  unfold criticalUpper
  field_simp
  ring

theorem criticalAnnulus_adjacent (j : ℕ) (d e : ℝ)
    (hd : d ∈ criticalAnnulus j) (he : e ∈ criticalAnnulus (j+1)) : 2*e < d := by
  have hd' := hd.1
  have he' := he.2
  rw [criticalUpper_succ] at he'
  linarith

theorem criticalUpper_antitone : Antitone criticalUpper := by
  intro i j hij
  unfold criticalUpper
  exact div_le_div_of_nonneg_left (by norm_num)
    (pow_pos (by norm_num : (0 : ℝ) < 4) i) (pow_le_pow_right₀ (by norm_num) hij)

theorem criticalAnnulus_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (criticalAnnulus i) (criticalAnnulus j) := by
  wlog hlt : i < j generalizing i j
  · exact (this hij.symm (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)).symm
  rw [Set.disjoint_left]
  intro d hdᵢ hdⱼ
  have hu := criticalUpper_antitone (Nat.succ_le_of_lt hlt)
  rw [criticalUpper_succ] at hu
  have hp := criticalUpper_pos i
  have hdi := hdᵢ.1
  have hdj := hdⱼ.2
  linarith

theorem measurable_criticalParameter (b : Bool) : Measurable (fun d => criticalParameter d b) := by
  unfold criticalParameter
  exact continuous_projIcc.measurable.comp (by cases b <;> fun_prop)

theorem criticalParameter_eq_sign (d : EntropyGap) (b : Bool) :
    criticalParameter d b = signParameter d b := by
  exact projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) (signParameter d b).property

/-- The clipping in the total definition is inactive on the entire gap support. -/
theorem criticalParameter_coe_of_mem (d : ℝ) (hd : d ∈ Ioc (0 : ℝ) (1/4))
    (b : Bool) : (criticalParameter d b : ℝ) = 1/2+(if b then d else -d) := by
  have hm : 1/2+(if b then d else -d) ∈ Icc (0 : ℝ) 1 := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> constructor <;> linarith [hd.1, hd.2]
  exact congrArg Subtype.val (projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) hm)

end ThresholdHC.CriticalEntropy
