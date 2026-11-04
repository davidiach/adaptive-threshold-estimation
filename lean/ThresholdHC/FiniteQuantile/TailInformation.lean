import ThresholdHC.FiniteQuantile.TailPair
import ThresholdHC.FiniteQuantile.FiniteInformation

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace ThresholdHC.FiniteQuantile
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.EntropyTailQuantile

/-- The information of the two actual tail priors, charged against work at
their population midpoint. The bound is uniform over the local cap. -/
theorem tail_information_ratio (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hs : μ.support.Finite) {ρ h : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hh : 0 ≤ h) (cap : ℕ) :
    informationRatio μ cap (midpointFourPriors (tailEndpoint μ hρ hρ1 hh false)
      (tailEndpoint μ hρ hρ1 hh true)) ≤ ENNReal.ofReal (h^2/4) := by
  let w := cutWeight (quantileThreshold μ ρ) (quantileBoundaryFraction μ ρ)
  let e := tailEpsilon h
  let low := tailEndpoint μ hρ hρ1 hh false
  let high := tailEndpoint μ hρ hρ1 hh true
  let mid := midpointPrior low high
  let M := fun n k (g : Gap) => w g * midpointMass g n k +
    (1-w g) * prefixLikelihood false n k g
  let D := fun n k (g : Gap) => 2*w g*e g *
    (prefixLikelihood true n k g - prefixLikelihood false n k g)
  let P := fun n k (g : Gap) => w g*(16*(e g)^2)*prefixEnergy g n k
  have hi := integrable_of_finite_gap_support μ hs
  have hw (g : Gap) : w g ∈ Icc (0:ℝ) 1 := cutWeight_range
    ⟨(quantileBoundaryFraction_properties μ hρ hρ1).1,
     (quantileBoundaryFraction_properties μ hρ hρ1).2.1⟩ g
  have hm (g : Gap) : mid.val g = w g / 2 := by
    dsimp [mid, midpointPrior, mixPrior, low, high, tailEndpoint, w, e]
    ring
  have hM (n k : ℕ) : prefixCoefficient μ mid n k = ∫ g, M n k g ∂μ := by
    unfold prefixCoefficient
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro g
    dsimp only
    rw [hm g]
    dsimp only [M, midpointMass]
    ring
  have hD (n k : ℕ) : prefixCoefficient μ high n k - prefixCoefficient μ low n k =
      ∫ g, D n k g ∂μ := by
    unfold prefixCoefficient
    rw [← integral_sub (hi _) (hi _)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro g
    dsimp [D, low, high, tailEndpoint, e, w]
    ring
  have hmid (g : Gap) (n k : ℕ) : 0 ≤ midpointMass g n k := by
    unfold midpointMass
    positivity [prefixLikelihood_nonneg true n k g, prefixLikelihood_nonneg false n k g]
  apply informationRatio_of_potential μ low high (h^2/4) (fun n k => ∫ g, P n k g ∂μ) _ _ _ cap
  · simp [P, prefixEnergy, posteriorEnergy, prefixLikelihood]
  · intro n k hk
    rw [midpoint_prefixReward μ low high n k hk, ← midpoint_prefixCoefficient μ low high n k hk]
    have hsq : (prefixCoefficient μ low n k - prefixCoefficient μ high n k)^2 =
        (prefixCoefficient μ high n k - prefixCoefficient μ low n k)^2 := by ring
    rw [hsq, hD, hM]
    apply mixture_quadratic_bound μ hs (D n k) (M n k) (P n k)
    · intro g
      exact add_nonneg (mul_nonneg (hw g).1 (hmid g n k))
        (mul_nonneg (sub_nonneg.mpr (hw g).2) (prefixLikelihood_nonneg false n k g))
    · intro g y
      have hlocal := fractional_word_bound
        (a := prefixLikelihood true n k g / 2) (b := prefixLikelihood false n k g / 2)
        (by positivity [prefixLikelihood_nonneg true n k g])
        (by positivity [prefixLikelihood_nonneg false n k g]) (hw g).1 (hw g).2 (e g) y
      dsimp [D,M,P,midpointMass,prefixEnergy]
      convert hlocal using 1; ring
  · intro n k hk
    rw [hM, ← integral_add (hi _) (hi _), ← integral_const_mul,
      ← integral_add (hi _) (hi _)]
    apply integral_mono (hi _) (hi _)
    intro g
    have he := tailEpsilon_bounds hh g
    have hsq := (sq_le_sq₀ (mul_nonneg he.1 g.property.1.le)
      (div_nonneg hh (by norm_num : (0:ℝ) ≤ 16))).mpr he.2.2
    have hscale : 64*(e g)^2*(g:ℝ)^2 ≤ h^2/4 := by nlinarith only [hsq]
    have hweight : 0 ≤ w g * (16*(e g)^2) := mul_nonneg (hw g).1 (by positivity)
    have hchildren := mul_le_mul_of_nonneg_left (prefixEnergy_step g hk) hweight
    have hpay := mul_le_mul_of_nonneg_right hscale (mul_nonneg (hw g).1 (hmid g n k))
    have hrest := mul_nonneg (div_nonneg (sq_nonneg h) (by norm_num : (0:ℝ) ≤ 4))
      (mul_nonneg (sub_nonneg.mpr (hw g).2) (prefixLikelihood_nonneg false n k g))
    dsimp only [P, M]
    nlinarith only [hchildren, hpay, hrest]

end ThresholdHC.FiniteQuantile
