import ThresholdHC.PoissonComparison.Affinity
import ThresholdHC.PoissonComparison.LogMoment
import ThresholdHC.AffineComparison.Moments
import ThresholdHC.AffineComparison.Testing

/-! Proofs of the targets of `Specification`: `lem:comparison` of
`research/2026-10-27-nonlinear-critical/affine_comparison.tex`, Poisson
case.

The proof is that of the categorical group `ThresholdHC.AffineComparison`,
with the Poisson log-moment `poissonLogMoment`, the Poisson moment generating
function `poissonVectorLaw_exp_integral` and the Poisson affinity
`poissonVectorLaw_affinity` in place of their categorical counterparts. The
uniform saddle `abstract_additive_certificate`, the exponential-moment bound
`squaredRisk_le_of_exponential_bounds` and the affinity test
`difference_le_of_affinity` are reused unchanged.

The constant `6` of `poisson_comparison_6` is a sharpening that comes only
from this Lean route and is not claimed by the source; the source constant
`12` is `poisson_comparison_12`, a corollary. `poisson_comparison_not_half`
shows that the statement is not vacuous: it fails for the constant `1/2`. -/

noncomputable section
open MeasureTheory Set
namespace ThresholdHC.PoissonComparison
open ThresholdHC.CriticalEntropy ThresholdHC.AffineComparison
open ThresholdHC.Tier6 (squaredRisk)

/-- `lem:comparison`, Poisson case, with constant `6`. This sharpens the
source constant `12`; the sharpening is a Lean-only result. -/
theorem poisson_comparison_6 : PoissonComparisonStatement 6 := by
  intro E _ _ _ X hXn hXc hXv J _ v ell hv G r hr hG η hη
  have hvc : Continuous v := v.continuous_of_finiteDimensional
  have helc : Continuous ell := ell.continuous_of_finiteDimensional
  have hpt : ∀ x ∈ X, ∀ y ∈ X, ∃ β : J → ℝ,
      0 ≤ poissonLogMoment (⇑v) x (-β)+poissonLogMoment (⇑v) y β+2*Real.log 2 →
      ell x-ell y < 2*(2*r+η/3) := by
    intro x hx y hy
    obtain ⟨β,hβ⟩ := poissonLogMoment_attained (⇑v) x y (hv x hx) (hv y hy)
    refine ⟨β,fun h0 => ?_⟩
    rw [hβ] at h0
    have hl : (∑ j, (Real.sqrt (v x j)-Real.sqrt (v y j))^2)/2 ≤ Real.log 2 := by linarith
    have haff : 1/2 ≤ (hellingerAffinity (poissonVectorLaw (v x))
        (poissonVectorLaw (v y))).toReal := by
      rw [poissonVectorLaw_affinity _ _ (hv x hx) (hv y hy)]
      have he : Real.exp (-Real.log 2) = 1/2 := by
        rw [Real.exp_neg,Real.exp_log (by norm_num)]
        norm_num
      rw [← he]
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      linarith
    have hd := difference_le_of_affinity _ _ G (measurable_of_countable G) (ell x) (ell y)
      r hr (hG x hx) (hG y hy) haff
    linarith
  obtain ⟨u,a,c,ha,haR,hb⟩ := abstract_additive_certificate X hXn hXc hXv
    (poissonLogMoment (⇑v)) ell helc
    (fun u => poissonLogMoment_parameter_continuousOn X v hvc u)
    (fun u => poissonLogMoment_parameter_concaveOn X hXv v u)
    (fun x _ => poissonLogMoment_score_continuous (⇑v) x)
    (fun x hx => poissonLogMoment_score_convexOn (⇑v) x (fun j => (hv x hx j).le))
    (fun x hx w => poissonLogMoment_diagonal (⇑v) x (fun j => (hv x hx j).le) w)
    (2*r+η/3) hpt
  refine ⟨u,c,fun x hx => ?_⟩
  have hR : 0 ≤ 2*r+η/3 := by positivity
  have h3 : 3*(2*r+η/3) = 6*r+η := by ring
  have hplus : (fun z : J → ℕ => Real.exp ((c+∑ j, u j*(z j : ℝ)-ell x)/a)) =
      (fun z => Real.exp ((c-ell x)/a+∑ j, (a⁻¹ • u) j*(z j : ℝ))) := by
    funext z
    congr 1
    simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,← Finset.mul_sum]
    field_simp
    ring
  have hminus : (fun z : J → ℕ => Real.exp (-(c+∑ j, u j*(z j : ℝ)-ell x)/a)) =
      (fun z => Real.exp ((ell x-c)/a+∑ j, (-(a⁻¹ • u)) j*(z j : ℝ))) := by
    funext z
    congr 1
    simp only [Pi.neg_apply,Pi.smul_apply,smul_eq_mul,neg_mul,Finset.sum_neg_distrib,
      mul_assoc,← Finset.mul_sum]
    field_simp
    ring
  rw [← h3]
  refine squaredRisk_le_of_exponential_bounds _ _ _
    (measurable_of_countable _).aestronglyMeasurable (2*r+η/3) a hR ha haR ?_ ?_ ?_ ?_
  · rw [hplus]
    exact poissonVectorLaw_exp_integrable _ _ _
  · rw [hminus]
    exact poissonVectorLaw_exp_integrable _ _ _
  · rw [hplus,poissonVectorLaw_exp_integral _ (fun j => (hv x hx j).le)]
    exact Real.exp_le_exp.mpr (hb x hx).1
  · rw [hminus,poissonVectorLaw_exp_integral _ (fun j => (hv x hx j).le)]
    exact Real.exp_le_exp.mpr (hb x hx).2

/-- `lem:comparison`, Poisson case, with the source constant `12`; a
corollary of `poisson_comparison_6`. -/
theorem poisson_comparison_12 : PoissonComparisonStatement 12 := by
  intro E _ _ _ X hXn hXc hXv J _ v ell hv G r hr hG η hη
  obtain ⟨β,c,h⟩ := poisson_comparison_6 E X hXn hXc hXv J v ell hv G r hr hG η hη
  refine ⟨β,c,fun x hx => (h x hx).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  nlinarith

/-- Squared risks without counts: the law over `Fin 0` is a Dirac mass. -/
theorem squaredRisk_fin_zero (w : Fin 0 → ℝ) (f : (Fin 0 → ℕ) → ℝ) (t : ℝ) :
    squaredRisk (poissonVectorLaw w) f t = ENNReal.ofReal ((f 0 - t)^2) := by
  have hf : ∀ z : Fin 0 → ℕ, f z = f 0 := fun z => congrArg f (Subsingleton.elim z 0)
  unfold squaredRisk
  simp only [hf,lintegral_const,measure_univ,mul_one]

/-- The conclusion is not vacuous: the constant `1/2` fails, with `X = [0,1]`,
`ell = id`, no counts and the constant estimator `1/2`. -/
theorem poisson_comparison_not_half : ¬ PoissonComparisonStatement (1/2) := by
  intro h
  obtain ⟨β,c,hc⟩ := h ℝ (Icc 0 1) ⟨0,by simp⟩ isCompact_Icc (convex_Icc 0 1) (Fin 0)
    (AffineMap.const ℝ ℝ (0 : Fin 0 → ℝ)) (AffineMap.id ℝ ℝ) (fun _ _ j => j.elim0)
    (fun _ => 1/2) (1/2) (by norm_num)
    (by
      intro x hx
      rw [squaredRisk_fin_zero]
      apply ENNReal.ofReal_le_ofReal
      simp only [AffineMap.id_apply]
      nlinarith [hx.1,hx.2])
    (1/8) (by norm_num)
  have h0 := hc 0 ⟨le_refl 0,zero_le_one⟩
  have h1 := hc 1 ⟨zero_le_one,le_refl 1⟩
  rw [squaredRisk_fin_zero,ENNReal.ofReal_le_ofReal_iff (by positivity)] at h0 h1
  simp only [Finset.univ_eq_empty,Finset.sum_empty,add_zero,AffineMap.id_apply] at h0 h1
  nlinarith

end ThresholdHC.PoissonComparison
