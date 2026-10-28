import ThresholdHC.UnbiasedConverse.ExperimentInformation
import ThresholdHC.UnbiasedConverse.TwoPoint
import ThresholdHC.UnbiasedConverse.Specification

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal Topology
namespace ThresholdHC.UnbiasedConverse
open ThresholdHC.Tier6

theorem tilted_modulus_bound {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    {V W h e : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hu : UniformlyUnbiased μ A) (hv : UniformVarianceBound μ A V)
    (hw : UniformBudget μ A W) (hh : 0 < h) (he : 0 < e) (he1 : e ≤ 1/8) :
    (modulus μ h)^2 * (1-4*e^2)^2 ≤ 16*h^2*W*(V+e^2*(modulus μ h)^2) := by
  let qp := tiltPlus h e hh he.le he1
  let qm := tiltMinus h e hh he.le he1
  have hlp (q : SignLaw) : MemLp (populationOutput A) 2 (experimentLaw μ A q) :=
    (evariance_lt_top_iff_memLp (measurable_populationOutput A).aestronglyMeasurable).mp
      (lt_of_le_of_lt (hv q) ENNReal.ofReal_lt_top)
  have hvar (q : SignLaw) : variance (populationOutput A) (experimentLaw μ A q) ≤ V := by
    simpa only [variance, ENNReal.toReal_ofReal hV] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hv q)
  have hk := tilt_experiment_information μ A hh he.le he1 hw
  have hpair := two_point_uniform_variance (experimentLaw μ A qp) (experimentLaw μ A qm)
    (hlp qp) (hlp qm) hV (show 0 ≤ tiltCoefficient h e*W by unfold tiltCoefficient; positivity)
    (hvar qp) (hvar qm) hk.1 hk.2
  rw [(hu qp).2,(hu qm).2] at hpair
  have hsep : signMean μ qp.val - signMean μ qm.val = 2*e*modulus μ h :=
    tilt_mean_separation μ hh he.le he1
  rw [hsep] at hpair
  have hd := tilt_denominator_pos he.le he1
  have hb := mul_le_mul_of_nonneg_right hpair (sq_nonneg (1-4*e^2))
  have heq : (tiltCoefficient h e * W * (2*V+(2*e*modulus μ h)^2/2)) * (1-4*e^2)^2 =
      32*(h*e)^2*W*(2*V+(2*e*modulus μ h)^2/2) := by
    unfold tiltCoefficient
    calc
      _ = (32*(h*e)^2/(1-4*e^2)^2*(1-4*e^2)^2) *
          (W*(2*V+(2*e*modulus μ h)^2/2)) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ (pow_ne_zero 2 hd.ne')]; ring
  rw [heq] at hb
  have hcancel : 0 < 4*e^2 := by positivity
  apply (mul_le_mul_iff_right₀ hcancel).mp
  nlinarith only [hb]

theorem modulus_square_bound {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    {V W : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hu : UniformlyUnbiased μ A) (hv : UniformVarianceBound μ A V)
    (hw : UniformBudget μ A W) {h : ℝ} (hh : 0 < h) :
    (modulus μ h)^2 ≤ 16*h^2*W*V := by
  let e : ℕ → ℝ := fun n => (1/8) * (1/((n:ℝ)+1))
  have he0 n : 0 < e n := by dsimp [e]; positivity
  have he1 n : e n ≤ 1/8 := by
    have hn : 1 ≤ (n:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) n]
    have hi : 1/((n:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr hn
    dsimp [e]; linarith
  have helim : Tendsto e atTop (𝓝 0) := by
    simpa [e] using tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  have hleft : Tendsto (fun n => (modulus μ h)^2*(1-4*(e n)^2)^2) atTop
      (𝓝 ((modulus μ h)^2)) := by
    convert tendsto_const_nhds.mul ((tendsto_const_nhds.sub
      (tendsto_const_nhds.mul (helim.pow 2))).pow 2) using 1 <;> norm_num
  have hright : Tendsto (fun n => 16*h^2*W*(V+(e n)^2*(modulus μ h)^2)) atTop
      (𝓝 (16*h^2*W*V)) := by
    simpa using tendsto_const_nhds.mul (tendsto_const_nhds.add
      ((helim.pow 2).mul tendsto_const_nhds))
  exact le_of_tendsto_of_tendsto' hleft hright
    (fun n => tilted_modulus_bound μ A hV hW hu hv hw hh (he0 n) (he1 n))

end ThresholdHC.UnbiasedConverse
