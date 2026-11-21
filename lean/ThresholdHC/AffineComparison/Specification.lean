import ThresholdHC.Tier6.TestingModel

/-! Target statements for the RMS affine comparison, categorical case.

Source: `research/2026-10-27-nonlinear-critical/affine_comparison.tex`,
section `An RMS comparison for finite convex experiments`, Lemma
`lem:comparison` (RMS affine comparison), case 1 (independent finite
categorical observations). The lemma is listed in the row `lem:comparison` of
`research/2026-10-27-nonlinear-critical/CHECKPOINT.md`, which records that the
note has no Lean verification.

* `CategoricalComparisonStatement C`: let `X` be a nonempty compact convex
  subset of a finite-dimensional real normed space and `ell` an affine
  functional. Observe `k` independent finite categorical variables
  `z i ∈ I i` whose probability vectors `p i x` are affine in `x` and strictly
  positive on `X`. If an arbitrary estimator `G` has squared risk at most
  `r^2` at every `x ∈ X`, then for every `η > 0` some additive estimator
  `c + ∑ i, φ i (z i)` has squared risk at most `(C*r+η)^2` at every
  `x ∈ X`.

The source proves `C = 12`. The Full module proves `C = 6`, and `C = 12` as a
corollary. The constant `6` is a sharpening obtained only by the Lean route
and is not a claim of the source: the source's total-variation testing step
(its display (4), with factor `sqrt (2/(1-sqrt 3/2))`) is replaced by the
direct affinity testing bound `S ≤ 2 r_G`, and its tail integral (5) by the
exponential-moment bound with the slightly coarser factor `3` (through
`CriticalEntropy.radius_second_moment_le`; the source's display (5) gives
`sqrt (1 + 2/log 2 + 2/(log 2)^2)`, about `2.84`). The whole improvement from
`12` to `6` comes from the testing step.

Deviations from the source.

* Only the categorical case is stated. The Poisson case of the same lemma
  is not part of this group.
* `r_G = sup_x (E_x (G - ell x)^2)^(1/2) < ∞` is replaced by an arbitrary
  bound `r ≥ 0` on every squared risk; taking `r = r_G` recovers the source.
  Risks are `Tier6.squaredRisk`, a lower integral in `[0,∞]`, so no
  integrability is assumed of `G`; square integrability of the produced
  estimator follows from its finite bound.
* `ell` is an affine map rather than a linear functional, which is slightly
  more general. Continuity of the affine maps is not assumed; it follows
  from finite dimensionality.
* The observations are indexed by `Fin k`, each with a finite type `I i`
  carrying a measurable-singleton sigma-algebra. The observation law `P_x` is
  the explicit product `categoricalProductLaw` of the finite Dirac sums
  `categoricalLaw`. Positivity and normalization of `p i x` are assumed only
  on `X`; off `X` the masses are truncated by `ENNReal.ofReal` and are
  irrelevant.
* Every function on the finite product is measurable, so `G` is arbitrary.
-/

noncomputable section
namespace ThresholdHC.AffineComparison
open MeasureTheory
open ThresholdHC.Tier6 (squaredRisk)

/-- The categorical law with masses `q a`. -/
def categoricalLaw {I : Type} [Fintype I] [MeasurableSpace I] (q : I → ℝ) : Measure I :=
  ∑ a, ENNReal.ofReal (q a) • Measure.dirac a

/-- Independent categorical observations `z i ∈ I i` with mass vectors `q i`. -/
def categoricalProductLaw {k : ℕ} {I : Fin k → Type} [∀ i, Fintype (I i)]
    [∀ i, MeasurableSpace (I i)] (q : ∀ i, I i → ℝ) : Measure (∀ i, I i) :=
  Measure.pi (fun i => categoricalLaw (q i))

/-- `lem:comparison`, categorical case, with constant `C` (the source has
`C = 12`; the Lean proof gives `C = 6`, a sharpening beyond the source). -/
def CategoricalComparisonStatement (C : ℝ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E), X.Nonempty → IsCompact X → Convex ℝ X →
  ∀ (k : ℕ) (I : Fin k → Type) [∀ i, Fintype (I i)] [∀ i, MeasurableSpace (I i)]
    [∀ i, MeasurableSingletonClass (I i)]
    (p : ∀ i, E →ᵃ[ℝ] (I i → ℝ)) (ell : E →ᵃ[ℝ] ℝ),
    (∀ x ∈ X, ∀ i a, 0 < p i x a) → (∀ x ∈ X, ∀ i, ∑ a, p i x a = 1) →
  ∀ (G : (∀ i, I i) → ℝ) (r : ℝ), 0 ≤ r →
    (∀ x ∈ X, squaredRisk (categoricalProductLaw (fun i => p i x)) G (ell x) ≤
      ENNReal.ofReal (r^2)) →
  ∀ η : ℝ, 0 < η → ∃ (φ : ∀ i, I i → ℝ) (c : ℝ), ∀ x ∈ X,
    squaredRisk (categoricalProductLaw (fun i => p i x))
      (fun z => c + ∑ i, φ i (z i)) (ell x) ≤ ENNReal.ofReal ((C*r+η)^2)

end ThresholdHC.AffineComparison
