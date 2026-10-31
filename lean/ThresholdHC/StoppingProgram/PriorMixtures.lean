import ThresholdHC.StoppingProgram.MomentImage
import ThresholdHC.StoppingProgram.FunctionMomentImage

/-! Convex mixtures of actual globally rare sign laws and their observable
target/count coefficients. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo ThresholdHC.CapIdentification

def mixPrior (q r : SignLaw) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) : SignLaw :=
  ⟨fun d => t*q.val d+(1-t)*r.val d,
    (measurable_const.mul q.property.1).add (measurable_const.mul r.property.1),fun d => by
      have hq := q.property.2 d
      have hr := r.property.2 d
      have ht' : 0 ≤ 1-t := by linarith [ht.2]
      constructor
      · exact add_nonneg (mul_nonneg ht.1 hq.1) (mul_nonneg ht' hr.1)
      · nlinarith [mul_le_mul_of_nonneg_left hq.2 ht.1,mul_le_mul_of_nonneg_left hr.2 ht']⟩

theorem mixPrior_integral (μ : Measure Gap) [IsProbabilityMeasure μ] (q r : SignLaw)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (g : Gap → ℝ) (hg : Integrable g μ) :
    (∫ d, (mixPrior q r t ht).val d*g d ∂μ) =
      t*(∫ d, q.val d*g d ∂μ)+(1-t)*(∫ d, r.val d*g d ∂μ) := by
  have he : (fun d => (mixPrior q r t ht).val d*g d) =
      fun d => t*(q.val d*g d)+(1-t)*(r.val d*g d) := by
    funext d
    dsimp only [mixPrior]
    ring
  rw [he,integral_add ((integrable_prior_function μ q hg).const_mul t)
    ((integrable_prior_function μ r hg).const_mul (1-t)),integral_const_mul,integral_const_mul]

theorem mixPrior_mean (μ : Measure Gap) [IsProbabilityMeasure μ] (q r : SignLaw)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    signMean μ (mixPrior q r t ht).val = t*signMean μ q.val+(1-t)*signMean μ r.val := by
  simpa only [mul_one,signMean] using mixPrior_integral μ q r t ht (fun _ => 1) (integrable_const _)

theorem mixPrior_rare (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ}
    (q r : SignLaw) (hq : RarePrior μ ρ q) (hr : RarePrior μ ρ r)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) : RarePrior μ ρ (mixPrior q r t ht) := by
  change signMean μ (mixPrior q r t ht).val ≤ ρ
  rw [mixPrior_mean]
  have h1 := mul_le_mul_of_nonneg_left hq ht.1
  have h2 := mul_le_mul_of_nonneg_left hr (show 0 ≤ 1-t by linarith [ht.2])
  nlinarith

theorem mixPrior_countCoefficient {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (s : CountState N) :
    countCoefficient μ (mixPrior q r t ht) s = t*countCoefficient μ q s+(1-t)*countCoefficient μ r s := by
  rw [countCoefficient_affine μ (mixPrior q r t ht),
    mixPrior_integral μ q r t ht _ ((polynomial_gap_memLp μ _).integrable (by norm_num)),
    countCoefficient_affine μ q,countCoefficient_affine μ r]
  ring

def midpointPrior (q r : SignLaw) : SignLaw := mixPrior q r (1/2) (by norm_num)

theorem midpointPrior_mean (μ : Measure Gap) [IsProbabilityMeasure μ] (q r : SignLaw) :
    signMean μ (midpointPrior q r).val = (signMean μ q.val+signMean μ r.val)/2 := by
  rw [midpointPrior,mixPrior_mean]
  ring

theorem midpointPrior_countCoefficient {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (s : CountState N) :
    countCoefficient μ (midpointPrior q r) s = (countCoefficient μ q s+countCoefficient μ r s)/2 := by
  rw [midpointPrior,mixPrior_countCoefficient]
  ring

end ThresholdHC.StoppingProgram
