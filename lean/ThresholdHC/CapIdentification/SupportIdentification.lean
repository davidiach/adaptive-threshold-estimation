import ThresholdHC.CapIdentification.OrthogonalContrast
import ThresholdHC.CapIdentification.RareContrast
import ThresholdHC.CapIdentification.BiasFloor

/-! Statistical target identification for arbitrary support: too many support
points give distinct rare priors with identical capped count laws. -/

noncomputable section
open MeasureTheory Polynomial Set
open scoped BigOperators ENNReal

namespace ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo
open ThresholdHC.StoppingProgram

theorem rare_indistinguishable_of_not_in_span (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ)
    (hnot : polynomialL2 μ 1 ∉ oddL2Span μ ((N+1)/2)) :
    ∃ qH qL : SignLaw, RarePrior μ ρ qH ∧ RarePrior μ ρ qL ∧
      CountMatch μ qH qL N ∧ 0 < signMean μ qH.val-signMean μ qL.val := by
  obtain ⟨a,hmom,hi,hpos⟩ := exists_polynomial_moment_contrast μ ((N+1)/2) hnot
  let H : ℝ[X] := 1-oddPolynomial a
  obtain ⟨M,hM⟩ := polynomial_gap_bound H
  have hb (d : Gap) : |1-(oddPolynomial a).eval (d:ℝ)| ≤ |M|+1 := by
    have hd := hM d
    simp only [H,eval_sub,eval_one,Real.norm_eq_abs] at hd
    exact hd.trans (by linarith [le_abs_self M])
  obtain ⟨qH,qL,hH,hL,hmatch,_,hgap⟩ := rare_priors_of_bounded_contrast μ ρ hρ hρ1 N
    (fun d => 1-(oddPolynomial a).eval (d:ℝ))
    (measurable_const.sub ((oddPolynomial a).continuous.measurable.comp measurable_subtype_coe))
    (|M|+1) (by positivity) hb hmom (by rwa [hi])
  exact ⟨qH,qL,hH,hL,(odd_moments_iff_count_match μ qH qL N).mp hmatch,hgap⟩

theorem rare_indistinguishable_of_large_support (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ)
    (S : Finset Gap) (hS : (S:Set Gap) ⊆ μ.support) (hcard : (N+1)/2 < S.card) :
    ∃ qH qL : SignLaw, RarePrior μ ρ qH ∧ RarePrior μ ρ qL ∧
      CountMatch μ qH qL N ∧ 0 < signMean μ qH.val-signMean μ qL.val :=
  rare_indistinguishable_of_not_in_span μ ρ hρ hρ1 N
    (constant_not_in_oddL2Span μ _ S hS hcard)

theorem infinite_support_rare_indistinguishable (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hμ : μ.support.Infinite) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ) :
    ∃ qH qL : SignLaw, RarePrior μ ρ qH ∧ RarePrior μ ρ qL ∧
      CountMatch μ qH qL N ∧ 0 < signMean μ qH.val-signMean μ qL.val :=
  rare_indistinguishable_of_not_in_span μ ρ hρ hρ1 N
    (constant_not_in_oddL2Span_infinite μ hμ _)

theorem infinite_support_program_floor (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hμ : μ.support.Infinite) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ B : ℝ, c ≤ programSquared μ ρ B N := by
  obtain ⟨qH,qL,hH,hL,hm,hgap⟩ := infinite_support_rare_indistinguishable μ hμ ρ hρ hρ1 N
  refine ⟨ENNReal.ofReal (((signMean μ qH.val-signMean μ qL.val)/2)^2),?_,?_⟩
  · exact ENNReal.ofReal_pos.mpr (sq_pos_of_pos (div_pos hgap (by norm_num)))
  · intro B
    exact matching_pair_program_floor μ ρ B N qH qL hH hL
      ((odd_moments_iff_count_match μ qH qL N).mpr hm)

end ThresholdHC.CapIdentification
