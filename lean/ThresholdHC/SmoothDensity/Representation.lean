import ThresholdHC.SmoothDensity.GapLaw

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace ThresholdHC.SmoothDensity
open ThresholdHC.Tier6

/-- Equality of the latent parameter law, tested against all bounded measurable
functions. The two mixture parameters are exactly the original Bernoulli parameters. -/
def Represents (μ : Measure Gap) (q : SignLaw) (f : ℝ → ℝ) : Prop :=
  ∀ (F : ℝ → ℝ), Measurable F → (∃ C : ℝ, ∀ p, |F p| ≤ C) →
    (∫ d, q.val d * F (1 / 2 + (d : ℝ)) + (1 - q.val d) * F (1 / 2 - (d : ℝ)) ∂μ) =
      ∫ p, f p * F p

/-- The whole density class is defined through the same hidden-gap experiment. -/
def SmoothModel (s : ℕ) (M : ℝ) (μ : Measure Gap) (q : SignLaw) : Prop :=
  ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ (∀ p, 0 ≤ f p) ∧
    (∀ p, p ∉ Icc (1 / 4 : ℝ) (3 / 4) → f p = 0) ∧
    (∫ p, f p) = 1 ∧
    (∀ k ≤ s, ∀ p, |iteratedDeriv k f p| ≤ M) ∧ Represents μ q f

theorem density_test_integral (s : ℕ) (t a : ℝ) (F : ℝ → ℝ)
    (hF : Measurable F) (C : ℝ) (hb : ∀ p, |F p| ≤ C) :
    (∫ p, density s t a p * F p) =
      ∫ x in Ioi (0 : ℝ),
        centeredDensity s t a x * F (1 / 2 + x) +
          centeredDensity s t a (-x) * F (1 / 2 - x) := by
  have hi : Integrable (fun x => centeredDensity s t a x * F (1 / 2 + x)) :=
    ((centeredDensity_contDiff s t a).continuous.integrable_of_hasCompactSupport
      (centeredDensity_compact s t a)).mul_bdd
      (hF.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb (1 / 2 + x)))
  have hn := hi.comp_neg
  have ht := integral_add_right_eq_self (μ := volume) (fun p => density s t a p * F p) (1 / 2 : ℝ)
  have he : (fun x => density s t a (x + 1 / 2) * F (x + 1 / 2)) =
      (fun x => centeredDensity s t a x * F (1 / 2 + x)) := by
    funext x
    unfold density
    rw [add_sub_cancel_right, add_comm x (1 / 2)]
  rw [he] at ht
  rw [← ht, ← integral_add_compl measurableSet_Ioi hi]
  simp only [compl_Ioi]
  rw [← integral_comp_neg_Ioi 0 (fun x => centeredDensity s t a x * F (1 / 2 + x))]
  simpa only [neg_zero,sub_eq_add_neg] using (integral_add hi.integrableOn hn.integrableOn).symm

theorem smooth_represents (s : ℕ) (t a : ℝ) (q : SignLaw)
    (hq : ∀ d, q.val d = 1 / 2 + a / 2 * perturbation s t d) :
    Represents smoothGapLaw q (density s t a) := by
  intro F hF ⟨C,hb⟩
  simp_rw [hq]
  rw [smoothGapLaw_integral (fun x => (1 / 2 + a / 2 * perturbation s t x) * F (1 / 2 + x) +
    (1 - (1 / 2 + a / 2 * perturbation s t x)) * F (1 / 2 - x)), density_test_integral s t a F hF C hb]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  simp only [centeredDensity, baseDensity_even, perturbation_odd]
  ring

theorem smooth_pair_in_class (s : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (plus : Bool),
      SmoothModel s M smoothGapLaw (smoothSign s ht ht1 plus) := by
  obtain ⟨M,hM,hbound⟩ := exists_uniform_density_bound s
  refine ⟨M,hM,?_⟩
  intro t ht ht1 plus
  let a : ℝ := if plus then 2 else -2
  have ha : |a| ≤ 2 := by cases plus <;> norm_num [a]
  refine ⟨density s t a,density_contDiff s t a,?_,density_supported s t a,
    density_integral s t a,hbound t a ht ht1 ha,?_⟩
  · intro p
    exact centeredDensity_nonneg s ht.le ht1 ha (p - 1 / 2)
  · apply smooth_represents
    intro d
    cases plus <;> norm_num [smoothSign, a]

end ThresholdHC.SmoothDensity
