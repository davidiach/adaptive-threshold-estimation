import ThresholdHC.ArbitraryLawAdaptation.CDFCoupling
import ThresholdHC.ArbitraryLawAdaptation.ZeroSelection

/-! CDF domination implies the square-root-three comparison, including an
unresolved atom at zero. The increasing coupling is constructed here. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval
namespace ThresholdHC.ArbitraryLawAdaptation

theorem cdfCoupling_closed_support (μ ν : Measure ℝ)
    (hμ : cdf μ (1/2) = 1) (hν : cdf ν (1/2) = 1) :
    ∀ᵐ z ∂cdfCoupling μ ν, z.1 ∈ Icc 0 (1/2) ∧ z.2 ∈ Icc 0 (1/2) := by
  have hm := (measurable_boundedQuantile (cdf μ) (by norm_num : (0 : ℝ) ≤ 1/2) hμ).prodMk
    (measurable_boundedQuantile (cdf ν) (by norm_num : (0 : ℝ) ≤ 1/2) hν)
  rw [cdfCoupling]
  apply (ae_map_iff hm.aemeasurable
    (p := fun z : ℝ × ℝ => z.1 ∈ Icc 0 (1/2) ∧ z.2 ∈ Icc 0 (1/2))
    ((measurable_fst measurableSet_Icc).inter (measurable_snd measurableSet_Icc))).mpr
  apply Filter.Eventually.of_forall
  intro u
  have h1 := boundedQuantile_properties (cdf μ) (by norm_num : (0 : ℝ) ≤ 1/2) hμ u
  have h2 := boundedQuantile_properties (cdf ν) (by norm_num : (0 : ℝ) ≤ 1/2) hν u
  exact ⟨⟨h1.1, h1.2.1⟩, ⟨h2.1, h2.2.1⟩⟩

theorem zeroSelection_le_sqrt_three_of_cdf (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ0 : μ (Iio 0) = 0) (hν0 : ν (Iio 0) = 0)
    (hμ : cdf μ (1/2) = 1) (hν : cdf ν (1/2) = 1)
    (hdom : ∀ x, cdf ν x ≤ cdf μ x) (ρ B : ℝ) :
    zeroSelection ν ρ B ≤ ENNReal.ofReal (Real.sqrt 3)*zeroSelection μ ρ B := by
  have hm := (measurable_boundedQuantile (cdf μ) (by norm_num : (0 : ℝ) ≤ 1/2) hμ).prodMk
    (measurable_boundedQuantile (cdf ν) (by norm_num : (0 : ℝ) ≤ 1/2) hν)
  have : IsProbabilityMeasure (cdfCoupling μ ν) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  have h := zeroSelection_increasing_coupling (cdfCoupling μ ν) (cdfCoupling_closed_support μ ν hμ hν)
    (cdfCoupling_increasing μ ν (by norm_num : (0 : ℝ) ≤ 1/2) hμ hν hdom) ρ B
  rw [(cdfCoupling_marginals μ ν hμ0 hν0 (by norm_num : (0 : ℝ) ≤ 1/2) hμ hν).1,
    (cdfCoupling_marginals μ ν hμ0 hν0 (by norm_num : (0 : ℝ) ≤ 1/2) hμ hν).2] at h
  exact h

end ThresholdHC.ArbitraryLawAdaptation
