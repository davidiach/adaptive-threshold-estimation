import ThresholdHC.SmoothDensity.Full
noncomputable section
open MeasureTheory InformationTheory Set ThresholdHC.SmoothDensity
open ThresholdHC.Tier6 ThresholdHC.Confidence
open scoped ENNReal ContDiff

example (k : ℕ) (x : ℝ) : |iteratedDeriv k profile x| ≤ k.factorial :=
  profile_derivative_bound k x

example {s k : ℕ} (hk : k ≤ s) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (x : ℝ) :
    |iteratedDeriv k (perturbation s t) x| ≤ k.factorial / 8 :=
  perturbation_derivative_bound hk ht ht1 x

example (s : ℕ) (t a : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (ha : |a| ≤ 2) :
    ContDiff ℝ ∞ (density s t a) ∧
    (∀ p, 0 ≤ density s t a p) ∧
    (∀ p, p ∉ Set.Icc (1 / 4 : ℝ) (3 / 4) → density s t a p = 0) ∧
    (∫ p, density s t a p) = 1 :=
  ⟨density_contDiff s t a,fun p => centeredDensity_nonneg s ht ht1 ha (p - 1 / 2),
    density_supported s t a,density_integral s t a⟩

example (s : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (t a : ℝ), 0 < t → t ≤ 1 → |a| ≤ 2 →
      ∀ k ≤ s, ∀ p, |iteratedDeriv k (density s t a) p| ≤ M :=
  exists_uniform_density_bound s

example (s : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 64) :
    t ^ (s + 1) / 8 * Real.log (1 / t) ≤
      (∫ x in Set.Ioi (0 : ℝ), centeredDensity s t 2 x) -
        ∫ x in Set.Ioi (0 : ℝ), centeredDensity s t (-2) x :=
  centered_pair_separation s ht ht1

example {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (η : Gap → ℝ) (hη : Measurable η)
    (hηb : ∀ d, 0 ≤ η d ∧ η d ≤ 1 / 8)
    (qp qm : SignLaw) (hp : ∀ d, qp.val d = 1 / 2 + η d)
    (hm : ∀ d, qm.val d = 1 / 2 - η d)
    (B h : ℝ) (hh : 0 < h) (hgap : ∀ d : Gap, (d : ℝ) * η d ≤ h / 8)
    (hwork : expectedWork μ A qp ≤ ENNReal.ofReal B) :
    klDiv (experimentLaw μ A qp) (experimentLaw μ A qm) ≤
      ENNReal.ofReal ((128 / 225 : ℝ) * h ^ 2 * B) :=
  hidden_local_pair_information μ A η hη hηb qp qm hp hm B h hh hgap hwork

example (s : ℕ) {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ radiusCutoff s) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 64 ∧
      t ^ (s + 1) = scaleConstant s * ε / Real.log (1 / ε) ∧
      2 * ε < t ^ (s + 1) / 8 * Real.log (1 / t) :=
  choose_smooth_scale s hε hsmall

example (s : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (plus : Bool),
      SmoothModel s M smoothGapLaw (smoothSign s ht ht1 plus) :=
  smooth_pair_in_class s

example (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (f : ℝ → ℝ) (h : Represents μ q f)
    (F : ℝ → ℝ) (hF : Measurable F) (C : ℝ) (hb : ∀ p, |F p| ≤ C) :
    (∫ p, F (p : ℝ) ∂latentLaw μ q) = ∫ p, f p * F p :=
  represents_latent_integral μ q f h F hF C hb

example (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (f : ℝ → ℝ) (h : Represents μ q f) :
    signMean μ q.val = ∫ p in Ioi (1 / 2 : ℝ), f p :=
  represents_threshold_mean μ q f h

example {s : ℕ} {M : ℝ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (h : SmoothModel s M μ q) {x : ℝ} (hx : 0 ≤ x) :
    μ.real {d : Gap | (d : ℝ) ≤ x} ≤ 2 * M * x :=
  smoothModel_cdf μ q h hx

example (s : ℕ) :
    ∃ M₀ c ε₀ : ℝ, 0 < M₀ ∧ 0 < c ∧ 0 < ε₀ ∧
      ∀ (M B ε δ : ℝ), M₀ ≤ M → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 4 →
      ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R),
        FitsClass s M B ε δ A →
          c * (ε ^ 2)⁻¹ * (Real.log (1 / ε)) ^ 2 * Real.log (1 / δ) ≤ B :=
  smooth_confidence_lower s

example (s : ℕ) :
    ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → ℝ → ℝ → AdaptiveEstimator R),
      ∀ M ε δ : ℝ, 1 ≤ M → 0 < ε → ε ≤ Real.exp (-16) → 0 < δ → δ ≤ 1 / 4 →
        FitsClass s M (upperBudget M ε δ) ε δ (rule M ε δ) :=
  smooth_confidence_upper s

example (s : ℕ) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R) (V W : ℝ),
        0 ≤ V → 0 ≤ W → ¬ FiniteUnbiasedClass s M V W A :=
  smooth_unbiased_impossible s

example (s : ℕ) :
    ∃ M₀ c ε₀ : ℝ, 1 ≤ M₀ ∧ 0 < c ∧ 0 < ε₀ ∧
      (∀ M B ε δ : ℝ, M₀ ≤ M → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 4 →
        ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R),
          FitsClass s M B ε δ A →
            c * (ε ^ 2)⁻¹ * Real.log (1 / ε) ^ 2 * Real.log (1 / δ) ≤ B) ∧
      (∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → ℝ → ℝ → AdaptiveEstimator R),
        ∀ M ε δ : ℝ, M₀ ≤ M → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 4 →
          FitsClass s M ((65536 * M) ^ 2 * (ε ^ 2)⁻¹ *
            Real.log (1 / ε) ^ 2 * Real.log (1 / δ)) ε δ (rule M ε δ)) ∧
      (∀ M : ℝ, M₀ ≤ M → ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R)
        (V W : ℝ), 0 ≤ V → 0 ≤ W → ¬ FiniteUnbiasedClass s M V W A) :=
  smooth_density_robustness s
#print axioms ThresholdHC.SmoothDensity.baseDensity_compact
#print axioms ThresholdHC.SmoothDensity.baseDensity_contDiff
#print axioms ThresholdHC.SmoothDensity.baseDensity_core
#print axioms ThresholdHC.SmoothDensity.baseDensity_even
#print axioms ThresholdHC.SmoothDensity.baseDensity_integrable
#print axioms ThresholdHC.SmoothDensity.baseDensity_integral
#print axioms ThresholdHC.SmoothDensity.baseDensity_nonneg
#print axioms ThresholdHC.SmoothDensity.baseDensity_zero
#print axioms ThresholdHC.SmoothDensity.baseDerivative_bounded
#print axioms ThresholdHC.SmoothDensity.centered_pair_separation
#print axioms ThresholdHC.SmoothDensity.choose_smooth_scale
#print axioms ThresholdHC.SmoothDensity.density_contDiff
#print axioms ThresholdHC.SmoothDensity.density_integral
#print axioms ThresholdHC.SmoothDensity.density_supported
#print axioms ThresholdHC.SmoothDensity.density_test_integral
#print axioms ThresholdHC.SmoothDensity.exists_uniform_density_bound
#print axioms ThresholdHC.SmoothDensity.gap_mul_perturbation_le
#print axioms ThresholdHC.SmoothDensity.hidden_local_pair_information
#print axioms ThresholdHC.SmoothDensity.hidden_reverse_pair_information
#print axioms ThresholdHC.SmoothDensity.linear_modulus
#print axioms ThresholdHC.SmoothDensity.local_pair_confidence_cost
#print axioms ThresholdHC.SmoothDensity.local_pair_information
#print axioms ThresholdHC.SmoothDensity.perturbation_abs_le
#print axioms ThresholdHC.SmoothDensity.perturbation_contDiff
#print axioms ThresholdHC.SmoothDensity.perturbation_derivative_bound
#print axioms ThresholdHC.SmoothDensity.perturbation_nonneg
#print axioms ThresholdHC.SmoothDensity.perturbation_odd
#print axioms ThresholdHC.SmoothDensity.perturbation_rational
#print axioms ThresholdHC.SmoothDensity.profile_contDiff
#print axioms ThresholdHC.SmoothDensity.profile_derivative_bound
#print axioms ThresholdHC.SmoothDensity.profile_iteratedDeriv
#print axioms ThresholdHC.SmoothDensity.radiusCutoff_pos
#print axioms ThresholdHC.SmoothDensity.represents_latent_integral
#print axioms ThresholdHC.SmoothDensity.represents_threshold_mean
#print axioms ThresholdHC.SmoothDensity.smoothGapLaw_integral
#print axioms ThresholdHC.SmoothDensity.smoothGapLaw_probability
#print axioms ThresholdHC.SmoothDensity.smoothModel_cdf
#print axioms ThresholdHC.SmoothDensity.smoothModel_envelope
#print axioms ThresholdHC.SmoothDensity.smoothSign_separation
#print axioms ThresholdHC.SmoothDensity.smooth_confidence_lower
#print axioms ThresholdHC.SmoothDensity.smooth_confidence_upper
#print axioms ThresholdHC.SmoothDensity.smooth_density_robustness
#print axioms ThresholdHC.SmoothDensity.smooth_pair_in_class
#print axioms ThresholdHC.SmoothDensity.smooth_represents
#print axioms ThresholdHC.SmoothDensity.smooth_unbiased_impossible
#print axioms ThresholdHC.SmoothDensity.upper_scale_bounds
