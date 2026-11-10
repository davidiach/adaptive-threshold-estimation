
import ThresholdHC.ArbitraryLawAdaptation.CDFCoupling
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval
open ThresholdHC.ArbitraryLawAdaptation

example : ∀ (f : StieltjesFunction ℝ) (u : I),
    boundedQuantile f u = sInf {x : ℝ | 0 ≤ x ∧ (u : ℝ) ≤ f x} := fun _ _ => rfl
example : ∀ (f : StieltjesFunction ℝ) {M : ℝ} (hM : 0 ≤ M) (hfM : f M = 1) (u : I),
    0 ≤ boundedQuantile f u ∧ boundedQuantile f u ≤ M ∧ (u : ℝ) ≤ f (boundedQuantile f u) :=
  @boundedQuantile_properties
example : ∀ (f : StieltjesFunction ℝ) {M : ℝ} (hM : 0 ≤ M) (hfM : f M = 1) (u : I) (x : ℝ),
    boundedQuantile f u ≤ x ↔ 0 ≤ x ∧ (u : ℝ) ≤ f x := @boundedQuantile_le_iff
example : ∀ (f : StieltjesFunction ℝ) {M : ℝ} (hM : 0 ≤ M) (hfM : f M = 1),
    Monotone (boundedQuantile f) := @boundedQuantile_monotone
example : ∀ (f : StieltjesFunction ℝ) {M : ℝ} (hM : 0 ≤ M) (hfM : f M = 1),
    Measurable (boundedQuantile f) := @measurable_boundedQuantile
example : ∀ (f g : StieltjesFunction ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hfM : f M = 1) (hgM : g M = 1) (hgf : ∀ x, g x ≤ f x) (u : I),
    boundedQuantile f u ≤ boundedQuantile g u := @boundedQuantile_antitone_cdf
example : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (hzero : μ (Iio 0) = 0)
    {M : ℝ} (hM : 0 ≤ M) (hμM : cdf μ M = 1),
    (volume : Measure I).map (boundedQuantile (cdf μ)) = μ := @boundedQuantile_map_volume
example : ∀ (μ ν : Measure ℝ), cdfCoupling μ ν =
    (volume : Measure I).map (fun u => (boundedQuantile (cdf μ) u, boundedQuantile (cdf ν) u)) :=
  fun _ _ => rfl
example : ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ0 : μ (Iio 0) = 0) (hν0 : ν (Iio 0) = 0) {M : ℝ} (hM : 0 ≤ M)
    (hμM : cdf μ M = 1) (hνM : cdf ν M = 1),
    (cdfCoupling μ ν).map Prod.fst = μ ∧ (cdfCoupling μ ν).map Prod.snd = ν :=
  @cdfCoupling_marginals
example : ∀ (μ ν : Measure ℝ) {M : ℝ} (hM : 0 ≤ M) (hμM : cdf μ M = 1)
    (hνM : cdf ν M = 1) (hdom : ∀ x, cdf ν x ≤ cdf μ x),
    ∀ᵐ z ∂cdfCoupling μ ν, z.1 ≤ z.2 := @cdfCoupling_increasing
example : ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ0 : μ (Iio 0) = 0) (hν0 : ν (Iio 0) = 0) {M : ℝ} (hM : 0 ≤ M)
    (hμM : cdf μ M = 1) (hνM : cdf ν M = 1) (hdom : ∀ x, cdf ν x ≤ cdf μ x),
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧
      π.map Prod.snd = ν ∧ (∀ᵐ z ∂π, z.1 ≤ z.2) := @exists_increasing_coupling_of_cdf
#print axioms ThresholdHC.ArbitraryLawAdaptation.boundedQuantile
#print axioms ThresholdHC.ArbitraryLawAdaptation.boundedQuantile_antitone_cdf
#print axioms ThresholdHC.ArbitraryLawAdaptation.boundedQuantile_le_iff
#print axioms ThresholdHC.ArbitraryLawAdaptation.boundedQuantile_map_volume
#print axioms ThresholdHC.ArbitraryLawAdaptation.boundedQuantile_monotone
#print axioms ThresholdHC.ArbitraryLawAdaptation.boundedQuantile_properties
#print axioms ThresholdHC.ArbitraryLawAdaptation.cdfCoupling
#print axioms ThresholdHC.ArbitraryLawAdaptation.cdfCoupling_increasing
#print axioms ThresholdHC.ArbitraryLawAdaptation.cdfCoupling_marginals
#print axioms ThresholdHC.ArbitraryLawAdaptation.exists_increasing_coupling_of_cdf
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurable_boundedQuantile
