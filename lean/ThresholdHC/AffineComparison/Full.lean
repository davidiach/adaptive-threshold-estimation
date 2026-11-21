import ThresholdHC.AffineComparison.Categorical
import ThresholdHC.AffineComparison.Testing

/-! Proofs of the targets of `Specification`: `lem:comparison` of
`research/2026-10-27-nonlinear-critical/affine_comparison.tex`, categorical
case.

The constant `6` of `categorical_comparison_6` is a sharpening that comes
only from this Lean route and is not claimed by the source; the source
constant `12` is `categorical_comparison_12`, a corollary. The factor `2`
(the half-diameter `S` of the affinity-`1/2` region is at most `2 r`) comes
from `affinity_squared_risk`; the factor `3` (squared risk at most `(3R)^2`
for every `R > S`) from the uniform saddle and the exponential-moment bound. -/

noncomputable section
open MeasureTheory Set
namespace ThresholdHC.AffineComparison
open ThresholdHC.CriticalEntropy
open ThresholdHC.Tier6 (squaredRisk)

/-- `lem:comparison`, categorical case, with constant `6`. This sharpens the
source constant `12`; the sharpening is a Lean-only result. -/
theorem categorical_comparison_6 : CategoricalComparisonStatement 6 := by
  intro E _ _ _ X hXn hXc hXv k I _ _ _ p ell hp hs G r hr hG η hη
  have hpc : ∀ i, Continuous (p i) := fun i => (p i).continuous_of_finiteDimensional
  have helc : Continuous ell := ell.continuous_of_finiteDimensional
  obtain ⟨x₀,hx₀⟩ := hXn
  have hne : ∀ i, Nonempty (I i) := by
    intro i
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := hs x₀ hx₀ i
    simp at h1
  have hprob : ∀ x ∈ X, IsProbabilityMeasure (categoricalProductLaw (fun i => p i x)) :=
    fun x hx => categoricalProductLaw_isProbabilityMeasure _
      (fun i a => (hp x hx i a).le) (hs x hx)
  have hpt : ∀ x ∈ X, ∀ y ∈ X, ∃ v : (∀ i, I i → ℝ),
      0 ≤ categoricalLogMoment (fun i => ⇑(p i)) x (-v)+
        categoricalLogMoment (fun i => ⇑(p i)) y v+2*Real.log 2 →
      ell x-ell y < 2*(2*r+η/3) := by
    intro x hx y hy
    obtain ⟨v,hv⟩ := categoricalLogMoment_attained p x y (hp x hx) (hp y hy)
    refine ⟨v,fun h0 => ?_⟩
    have hA : 0 < ∏ i, realFiniteAffinity (p i x) (p i y) := Finset.prod_pos
      (fun i _ => realFiniteAffinity_pos (p i x) (p i y) (hp x hx i) (hp y hy i))
    rw [hv] at h0
    have hl : 0 ≤ Real.log ((∏ i, realFiniteAffinity (p i x) (p i y))*2) := by
      rw [Real.log_mul hA.ne' (by norm_num)]
      linarith
    have hb := (Real.log_nonneg_iff (by positivity)).mp hl
    have := hprob x hx
    have := hprob y hy
    have haff : 1/2 ≤ (hellingerAffinity (categoricalProductLaw (fun i => p i x))
        (categoricalProductLaw (fun i => p i y))).toReal := by
      rw [categoricalProductLaw_affinity _ _ (fun i a => (hp x hx i a).le)
        (fun i a => (hp y hy i a).le)]
      linarith
    have hd := difference_le_of_affinity _ _ G (measurable_of_countable G) (ell x) (ell y)
      r hr (hG x hx) (hG y hy) haff
    linarith
  obtain ⟨u,a,c,ha,haR,hb⟩ := abstract_additive_certificate X ⟨x₀,hx₀⟩ hXc hXv
    (categoricalLogMoment (fun i => ⇑(p i))) ell helc
    (fun u => categoricalLogMoment_parameter_continuousOn X p hpc hp u)
    (fun u => categoricalLogMoment_parameter_concaveOn X hXv p hp u)
    (fun x hx => categoricalLogMoment_score_continuous p x (hp x hx))
    (fun x hx => categoricalLogMoment_score_convexOn p x (hp x hx))
    (fun x hx w => categoricalLogMoment_diagonal p x (hp x hx) (hs x hx) w)
    (2*r+η/3) hpt
  refine ⟨u,c,fun x hx => ?_⟩
  have := hprob x hx
  have hR : 0 ≤ 2*r+η/3 := by positivity
  have h3 : 3*(2*r+η/3) = 6*r+η := by ring
  rw [← h3]
  refine squaredRisk_le_of_exponential_bounds _ _ _
    (measurable_of_countable _).aestronglyMeasurable (2*r+η/3) a hR ha haR
    (finite_function_integrable _ _) (finite_function_integrable _ _) ?_ ?_
  · have he : (fun z : ∀ i, I i => Real.exp ((c+∑ i, u i (z i)-ell x)/a)) =
        (fun z => Real.exp ((c-ell x)/a+∑ i, (a⁻¹ • u) i (z i))) := by
      funext z
      congr 1
      simp only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum]
      ring
    rw [he,categorical_exp_integral _ (hp x hx)]
    exact Real.exp_le_exp.mpr (hb x hx).1
  · have he : (fun z : ∀ i, I i => Real.exp (-(c+∑ i, u i (z i)-ell x)/a)) =
        (fun z => Real.exp ((ell x-c)/a+∑ i, (-(a⁻¹ • u)) i (z i))) := by
      funext z
      congr 1
      simp only [Pi.neg_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_neg_distrib,
        ← Finset.mul_sum]
      ring
    rw [he,categorical_exp_integral _ (hp x hx)]
    exact Real.exp_le_exp.mpr (hb x hx).2

/-- `lem:comparison`, categorical case, with the source constant `12`; a
corollary of `categorical_comparison_6`. -/
theorem categorical_comparison_12 : CategoricalComparisonStatement 12 := by
  intro E _ _ _ X hXn hXc hXv k I _ _ _ p ell hp hs G r hr hG η hη
  obtain ⟨φ,c,h⟩ := categorical_comparison_6 E X hXn hXc hXv k I p ell hp hs G r hr hG η hη
  refine ⟨φ,c,fun x hx => (h x hx).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  nlinarith

end ThresholdHC.AffineComparison
