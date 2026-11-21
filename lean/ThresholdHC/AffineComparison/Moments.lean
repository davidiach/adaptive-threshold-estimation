import ThresholdHC.AffineComparison.Specification
import ThresholdHC.CriticalEntropy.FiniteRMS

/-! Squared risk from two exponential-moment bounds, on an arbitrary
probability space. The radius `R` and scale `a ≤ R / log 2` give squared
risk at most `(3R)^2`, through `second_moment_of_exponential_bounds` and
`radius_second_moment_le`; no tail integral is needed. -/

noncomputable section
open MeasureTheory
namespace ThresholdHC.AffineComparison
open ThresholdHC.CriticalEntropy
open ThresholdHC.Tier6 (squaredRisk)

theorem squaredRisk_le_of_exponential_bounds {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (θ : ℝ)
    (hf : AEStronglyMeasurable f μ) (R a : ℝ) (hR : 0 ≤ R) (ha : 0 < a)
    (haR : a ≤ R/Real.log 2)
    (hp : Integrable (fun ω => Real.exp ((f ω-θ)/a)) μ)
    (hm : Integrable (fun ω => Real.exp (-(f ω-θ)/a)) μ)
    (hpb : (∫ ω, Real.exp ((f ω-θ)/a) ∂μ) ≤ Real.exp (R/a-Real.log 2))
    (hmb : (∫ ω, Real.exp (-(f ω-θ)/a) ∂μ) ≤ Real.exp (R/a-Real.log 2)) :
    squaredRisk μ f θ ≤ ENNReal.ofReal ((3*R)^2) := by
  have hX : AEStronglyMeasurable (fun ω => f ω-θ) μ := hf.sub aestronglyMeasurable_const
  obtain ⟨hL,hI⟩ := second_moment_of_exponential_bounds μ (fun ω => f ω-θ) hX
    R a hR ha hp hm hpb hmb
  have hint := (memLp_two_iff_integrable_sq hX).mp hL
  unfold squaredRisk
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [radius_second_moment_le R a hR ha haR]

end ThresholdHC.AffineComparison
