import ThresholdHC.CapIdentification.SupportIdentification

/-! Exact statistical target-identification threshold for a law supported
on finitely many distinct positive magnitudes. -/

noncomputable section
open MeasureTheory Polynomial Set
open scoped BigOperators

namespace ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo

theorem finset_odd_interpolation (S : Finset Gap) :
    ∃ a : Fin S.card → ℝ, ∀ d ∈ S, (oddPolynomial a).eval (d:ℝ) = 1 := by
  classical
  let e := S.equivFin
  let d : Fin S.card → ℝ := fun i => ((e.symm i).val:ℝ)
  have hd (i : Fin S.card) : 0 < d i := (e.symm i).val.property.1
  have hinj : Function.Injective d := by
    intro i j hij
    apply e.symm.injective
    exact Subtype.ext (Subtype.ext hij)
  obtain ⟨a,ha⟩ := odd_interpolation d hd hinj
  refine ⟨a,?_⟩
  intro x hx
  have he := ha (e ⟨x,hx⟩)
  simpa only [d,Equiv.symm_apply_apply,oddPolynomial_eval] using he

theorem finite_support_target_of_moments (μ : Measure Gap) [IsFiniteMeasure μ]
    (S : Finset Gap) (hS : μ.support ⊆ (S:Set Gap)) (L : ℕ) (hL : S.card ≤ L)
    (qH qL : SignLaw)
    (hmom : ∀ j : Fin L, ∫ d, (qH.val d-qL.val d)*(d:ℝ)^(2*j.val+1) ∂μ = 0) :
    signMean μ qH.val = signMean μ qL.val := by
  obtain ⟨a,ha⟩ := finset_odd_interpolation S
  let F := weightedPolynomialIntegral μ (fun d => qH.val d-qL.val d) (fun d => (d:ℝ))
    (qH.property.1.sub qL.property.1) measurable_subtype_coe (signDifference_norm qH qL)
    (fun d => ⟨d.property.1.le,by linarith [d.property.2]⟩)
  have hmon (j : Fin S.card) : F (X^(2*j.val+1)) = 0 := by
    change (∫ d, (qH.val d-qL.val d)*(X^(2*j.val+1):ℝ[X]).eval (d:ℝ) ∂μ) = 0
    simpa only [eval_pow,eval_X] using hmom ⟨j.val,lt_of_lt_of_le j.isLt hL⟩
  have hpoly : F (oddPolynomial a) = 0 := by
    simp only [oddPolynomial,C_mul',map_sum,map_smul,smul_eq_mul]
    exact Finset.sum_eq_zero (fun j _ => by rw [hmon j,mul_zero])
  have he : F (oddPolynomial a) = ∫ d, qH.val d-qL.val d ∂μ := by
    apply integral_congr_ae
    filter_upwards [μ.support_mem_ae] with d hd
    rw [ha d (hS hd),mul_one]
  have hint (q : SignLaw) : Integrable q.val μ := Integrable.of_bound q.property.1.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun d => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (q.property.2 d).1] using (q.property.2 d).2))
  apply sub_eq_zero.mp
  rw [signMean,signMean,← integral_sub (hint qH) (hint qL),← he,hpoly]

def CapDeterminesTarget (μ : Measure Gap) (ρ : ℝ) (N : ℕ) : Prop :=
  ∀ qH qL : SignLaw, RarePrior μ ρ qH → RarePrior μ ρ qL → CountMatch μ qH qL N →
    signMean μ qH.val = signMean μ qL.val

theorem finite_support_target_threshold (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ)
    (S : Finset Gap) (hS : μ.support = (S:Set Gap)) (hcard : 0 < S.card) :
    CapDeterminesTarget μ ρ N ↔ 2*S.card-1 ≤ N := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨qH,qL,hH,hL,hm,hgap⟩ := rare_indistinguishable_of_large_support μ ρ hρ hρ1 N S
      (by rw [hS]) (by omega)
    have he := h qH qL hH hL hm
    rw [he,sub_self] at hgap
    exact (lt_irrefl _ hgap)
  · intro hn qH qL _ _ hm
    exact finite_support_target_of_moments μ S (by rw [hS]) ((N+1)/2) (by omega) qH qL
      ((odd_moments_iff_count_match μ qH qL N).mpr hm)

theorem infinite_support_target_not_identified (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hμ : μ.support.Infinite) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ) :
    ¬CapDeterminesTarget μ ρ N := by
  intro h
  obtain ⟨qH,qL,hH,hL,hm,hgap⟩ := infinite_support_rare_indistinguishable μ hμ ρ hρ hρ1 N
  rw [h qH qL hH hL hm,sub_self] at hgap
  exact (lt_irrefl _ hgap)

end ThresholdHC.CapIdentification
