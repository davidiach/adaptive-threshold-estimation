import ThresholdHC.Genie.UniformGapModel
import ThresholdHC.Genie.UniformMoments

/-! Exact uniform-mixture prefix moments and the variance-reference moments
in the explicit infinite-divergence example. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram
open ThresholdHC.CapIdentification

theorem uniformGap_symmetrize (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ d : Gap, f (1/2+d.val)+f (1/2-d.val) ∂uniformGapLaw) =
      2*(∫ p in (0:ℝ)..1, f p) := by
  rw [uniformGap_integral (fun x : ℝ => f (1/2+x)+f (1/2-x))]
  have hp : IntervalIntegrable (fun x : ℝ => f (1/2+x)) volume 0 (1/2) :=
    (hf.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hm : IntervalIntegrable (fun x : ℝ => f (1/2-x)) volume 0 (1/2) :=
    (hf.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hp hm,intervalIntegral.integral_comp_add_left,
    intervalIntegral.integral_comp_sub_left]
  norm_num only [add_zero,sub_zero,sub_self,show (1/2:ℝ)+1/2 = 1 by norm_num]
  rw [add_comm,intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 (1/2)) (hf.intervalIntegrable (1/2) 1)]

def uniformSignPrior : SignLaw := constantPrior (1/2) (by norm_num)

theorem uniform_prefix_moment (n k : ℕ) :
    prefixCoefficient uniformGapLaw uniformSignPrior n k = uniformMoment k (n-k) := by
  have h := uniformGap_symmetrize (uniformMonomial k (n-k)) (uniformMonomial_continuous _ _)
  have he : prefixCoefficient uniformGapLaw uniformSignPrior n k =
      (1/2)*(∫ d : Gap, uniformMonomial k (n-k) (1/2+d.val)+uniformMonomial k (n-k) (1/2-d.val) ∂uniformGapLaw) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun d => by
      simp [prefixCoefficient,uniformSignPrior,constantPrior,prefixLikelihood,uniformMonomial]
      <;> ring)
  rw [he,h]
  unfold uniformMoment
  ring

theorem singular_variance_prefix_moment (n k : ℕ) :
    prefixCoefficient uniformGapLaw singularVariancePrior n k = 2*uniformMoment k (n-k+1) := by
  have h := uniformGap_symmetrize (uniformMonomial k (n-k+1)) (uniformMonomial_continuous _ _)
  calc
    _ = ∫ d : Gap, uniformMonomial k (n-k+1) (1/2+d.val)+uniformMonomial k (n-k+1) (1/2-d.val) ∂uniformGapLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun d => by
        simp only [singularVariancePrior,prefixLikelihood,ite_true,Bool.false_eq_true,ite_false,
          uniformMonomial,pow_succ]
        have h1 : (1:ℝ)-(1/2+d.val) = 1/2-d.val := by ring
        have h0 : (1:ℝ)-(1/2-d.val) = 1/2+d.val := by ring
        rw [h1,h0]
        ring)
    _ = _ := h

theorem singular_prefix_gap (n k : ℕ) :
    |prefixCoefficient uniformGapLaw singularExamplePriors.high n k-
      prefixCoefficient uniformGapLaw singularExamplePriors.low n k| ≤
        uniformMoment k (n-k)/2 := by
  have hiP := integrable_prefixLikelihood uniformGapLaw true n k
  have hiM := integrable_prefixLikelihood uniformGapLaw false n k
  have hp : 0 ≤ ∫ d, prefixLikelihood true n k d ∂uniformGapLaw :=
    integral_nonneg (fun d => prefixLikelihood_nonneg true n k d)
  have hm : 0 ≤ ∫ d, prefixLikelihood false n k d ∂uniformGapLaw :=
    integral_nonneg (fun d => prefixLikelihood_nonneg false n k d)
  have hu := uniform_prefix_moment n k
  simp only [prefixCoefficient,uniformSignPrior,singularExamplePriors,constantPrior,nullSignLaw,
    zero_mul,sub_zero,one_mul,zero_add] at hu ⊢
  rw [integral_add (hiP.const_mul _) (hiM.const_mul _),integral_const_mul,integral_const_mul] at hu
  rw [integral_add (hiP.const_mul _) (hiM.const_mul _),integral_const_mul,integral_const_mul]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem singular_work_prefix (n k : ℕ) :
    uniformMoment k (n-k)/2 ≤ prefixCoefficient uniformGapLaw singularExamplePriors.work n k := by
  have hiP := integrable_prefixLikelihood uniformGapLaw true n k
  have hiM := integrable_prefixLikelihood uniformGapLaw false n k
  have hm : 0 ≤ ∫ d, prefixLikelihood false n k d ∂uniformGapLaw :=
    integral_nonneg (fun d => prefixLikelihood_nonneg false n k d)
  have hu := uniform_prefix_moment n k
  simp only [prefixCoefficient,uniformSignPrior,singularExamplePriors,constantPrior] at hu ⊢
  rw [integral_add (hiP.const_mul _) (hiM.const_mul _),integral_const_mul,integral_const_mul] at hu ⊢
  linarith

end ThresholdHC.Genie
