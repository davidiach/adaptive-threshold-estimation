import ThresholdHC.StoppingProgram.RaritySupport

/-! Equality in the upper-tail bound forces the optimizer to select all
values above the cutoff and no values below it, almost everywhere. -/

noncomputable section
open MeasureTheory

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo

theorem prior_excess_le_positive {u x : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) : u*x ≤ max x 0 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
    nlinarith [hu.1,hu.2]
  · rw [max_eq_right (le_of_not_ge hx)]
    exact mul_nonpos_of_nonneg_of_nonpos hu.1 (le_of_not_ge hx)

theorem upper_tail_equality_cutoff (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ ell : ℝ} (hell : 0 ≤ ell) (f : Gap → ℝ) (hi : Integrable f μ)
    (q : SignLaw) (hq : RarePrior μ ρ q)
    (he : (∫ d, q.val d*f d ∂μ) = ρ*ell+∫ d, max (f d-ell) 0 ∂μ) :
    ell*(ρ-signMean μ q.val) = 0 ∧
      ∀ᵐ d ∂μ, (ell < f d → q.val d = 1) ∧ (f d < ell → q.val d = 0) := by
  let gap : Gap → ℝ := fun d => max (f d-ell) 0-q.val d*(f d-ell)
  have hgap0 (d : Gap) : 0 ≤ gap d := sub_nonneg.mpr (prior_excess_le_positive (q.property.2 d))
  have hgap : Integrable gap μ := (hi.sub (integrable_const ell)).pos_part.sub
    (integrable_prior_function μ q (hi.sub (integrable_const ell)))
  have hint : (∫ d, gap d ∂μ) = ell*(signMean μ q.val-ρ) := by
    change (∫ d, max (f d-ell) 0-q.val d*(f d-ell) ∂μ) = _
    have hadd := integral_sub (hi.sub (integrable_const ell)).pos_part
      (integrable_prior_function μ q (hi.sub (integrable_const ell)))
    simp only [Pi.sub_apply] at hadd
    rw [hadd]
    rw [← prior_excess_integral μ q f hi ell,he]
    ring
  have hzero : (∫ d, gap d ∂μ) = 0 := by
    apply le_antisymm _ (integral_nonneg hgap0)
    rw [hint]
    exact mul_nonpos_of_nonneg_of_nonpos hell (sub_nonpos.mpr hq)
  have hae := (integral_eq_zero_iff_of_nonneg (fun d => hgap0 d) hgap).mp hzero
  refine ⟨by rw [hint] at hzero; nlinarith,?_⟩
  filter_upwards [hae] with d hd
  change max (f d-ell) 0-q.val d*(f d-ell) = 0 at hd
  constructor
  · intro hlt
    rw [max_eq_left (by linarith : 0 ≤ f d-ell)] at hd
    nlinarith
  · intro hlt
    rw [max_eq_right (by linarith : f d-ell ≤ 0)] at hd
    nlinarith

end ThresholdHC.StoppingProgram
