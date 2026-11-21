import ThresholdHC.Tier6.TestingModel
import Mathlib.Probability.Distributions.Poisson.Basic

/-! Target statements for the RMS affine comparison, Poisson case.

Source: `research/2026-10-27-nonlinear-critical/affine_comparison.tex`,
section `An RMS comparison for finite convex experiments`, Lemma
`lem:comparison` (RMS affine comparison), case 2 (a finite vector of
independent Poisson counts whose strictly positive intensities `v_j(x)` are
affine in `x`; additive class `c + ∑ j, β j * z j`). The lemma is listed in
the row `lem:comparison` of
`research/2026-10-27-nonlinear-critical/CHECKPOINT.md`, which records that the
note has no Lean verification. The categorical case of the same lemma is the
group `ThresholdHC.AffineComparison`.

* `PoissonComparisonStatement C`: let `X` be a nonempty compact convex
  subset of a finite-dimensional real normed space and `ell` an affine
  functional. Observe independent Poisson counts `z j`, `j ∈ J` finite, whose
  intensities `v x j` are affine in `x` and strictly positive on `X`. If an
  arbitrary estimator `G` has squared risk at most `r^2` at every `x ∈ X`,
  then for every `η > 0` some additive estimator `c + ∑ j, β j * z j` has
  squared risk at most `(C*r+η)^2` at every `x ∈ X`.

The source proves `C = 12`. The Full module proves `C = 6`, and `C = 12` as a
corollary. The constant `6` is a sharpening obtained only by the Lean route
and is not a claim of the source: the source's total-variation testing step
(its display (4)) is replaced by the direct affinity testing bound
`S ≤ 2 r_G`, and its tail integral (5) by the exponential-moment bound with
factor `3`, exactly as in the categorical group.

Deviations from the source.

* `r_G = sup_x (E_x (G - ell x)^2)^(1/2) < ∞` is replaced by an arbitrary
  bound `r ≥ 0` on every squared risk; taking `r = r_G` recovers the source.
  Risks are `Tier6.squaredRisk`, a lower integral in `[0,∞]`, so no
  integrability is assumed of `G`; square integrability of the produced
  estimator follows from its finite bound.
* `ell` is an affine map rather than a linear functional, which is slightly
  more general. Continuity of the affine maps is not assumed; it follows
  from finite dimensionality.
* The finite vector of counts is indexed by an arbitrary finite type `J`.
  The intensity map `v` is affine on all of `E`, with positivity assumed only
  on `X`. The observation law `P_x` is the explicit product
  `poissonVectorLaw (v x)` of Mathlib's `poissonMeasure`; intensities enter
  through `Real.toNNReal`, which is exact wherever they are nonnegative, so
  in particular on `X`.
* Every function on the countable discrete space `J → ℕ` is measurable, so
  `G` is arbitrary.
-/

noncomputable section
namespace ThresholdHC.PoissonComparison
open MeasureTheory ProbabilityTheory
open ThresholdHC.Tier6 (squaredRisk)

/-- Independent Poisson counts `z j` with intensities `w j` (entered through
`Real.toNNReal`, exact wherever `w j ≥ 0`). -/
def poissonVectorLaw {J : Type} [Fintype J] (w : J → ℝ) : Measure (J → ℕ) :=
  Measure.pi (fun j => poissonMeasure (w j).toNNReal)

/-- `lem:comparison`, Poisson case, with constant `C` (the source has
`C = 12`; the Lean proof gives `C = 6`, a sharpening beyond the source). -/
def PoissonComparisonStatement (C : ℝ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E), X.Nonempty → IsCompact X → Convex ℝ X →
  ∀ (J : Type) [Fintype J] (v : E →ᵃ[ℝ] (J → ℝ)) (ell : E →ᵃ[ℝ] ℝ),
    (∀ x ∈ X, ∀ j, 0 < v x j) →
  ∀ (G : (J → ℕ) → ℝ) (r : ℝ), 0 ≤ r →
    (∀ x ∈ X, squaredRisk (poissonVectorLaw (v x)) G (ell x) ≤ ENNReal.ofReal (r^2)) →
  ∀ η : ℝ, 0 < η → ∃ (β : J → ℝ) (c : ℝ), ∀ x ∈ X,
    squaredRisk (poissonVectorLaw (v x)) (fun z => c + ∑ j, β j * (z j : ℝ)) (ell x) ≤
      ENNReal.ofReal ((C*r+η)^2)

end ThresholdHC.PoissonComparison
