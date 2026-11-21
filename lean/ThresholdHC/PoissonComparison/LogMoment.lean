import ThresholdHC.PoissonComparison.Specification
import ThresholdHC.AffineComparison.Saddle

/-! The Poisson log-moment of an additive score,
`Λ x β = ∑ j, v x j * (exp (β j) - 1)`, which is `log E_x exp (∑ j, β j z j)`
under the Poisson vector law when the intensities `v x j` are nonnegative. It
is affine, hence concave and continuous, in the parameter `x`, and convex and
continuous in the score `β`; its diagonal `Λ x β + Λ x (-β)` is nonnegative,
and the two-point value `Λ x (-β) + Λ y β` equals
`-∑ j, (sqrt (v x j) - sqrt (v y j))^2` at
`β j = log (sqrt (v x j)) - log (sqrt (v y j))` (this is its infimum, which is
not needed and not proved here). -/

noncomputable section
open Set
namespace ThresholdHC.PoissonComparison
open ThresholdHC.AffineComparison

/-- The log-moment of the additive score `β` under intensities `v x` (for
nonnegative intensities). -/
def poissonLogMoment {E J : Type} [Fintype J] (v : E → J → ℝ) (x : E) (β : J → ℝ) : ℝ :=
  ∑ j, v x j * (Real.exp (β j) - 1)

section Curvature

variable {E : Type} {J : Type} [Fintype J]

theorem poissonLogMoment_parameter_continuousOn [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E)
    (v : E →ᵃ[ℝ] (J → ℝ)) (hvc : Continuous v) (u : J → ℝ) :
    ContinuousOn (fun x => poissonLogMoment v x u) X := by
  unfold poissonLogMoment
  apply Continuous.continuousOn
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp hvc).mul continuous_const

theorem poissonLogMoment_parameter_concaveOn [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXv : Convex ℝ X)
    (v : E →ᵃ[ℝ] (J → ℝ)) (u : J → ℝ) :
    ConcaveOn ℝ X (fun x => poissonLogMoment v x u) := by
  refine ⟨hXv,?_⟩
  intro x _ y _ a b _ _ hab
  apply le_of_eq
  have hc : v (a • x + b • y) = a • v x + b • v y := Convex.combo_affine_apply hab
  simp only [poissonLogMoment,hc,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem poissonLogMoment_score_continuous (v : E → J → ℝ) (x : E) :
    Continuous (poissonLogMoment v x) := by
  unfold poissonLogMoment
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul ((Real.continuous_exp.comp (continuous_apply j)).sub
    continuous_const)

theorem poissonLogMoment_score_convexOn (v : E → J → ℝ) (x : E) (hx : ∀ j, 0 ≤ v x j) :
    ConvexOn ℝ univ (poissonLogMoment v x) := by
  unfold poissonLogMoment
  apply convexOn_finset_sum convex_univ
  intro j _
  have h := convexOn_exp.comp_linearMap (LinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) j)
  rw [preimage_univ] at h
  have h2 := (h.smul (hx j)).add_const (-(v x j))
  refine h2.congr (fun β _ => ?_)
  simp only [Pi.add_apply,Function.comp_apply,LinearMap.coe_proj,Function.eval,smul_eq_mul]
  ring

theorem poissonLogMoment_diagonal (v : E → J → ℝ) (x : E) (hx : ∀ j, 0 ≤ v x j)
    (w : J → ℝ) :
    0 ≤ poissonLogMoment v x w + poissonLogMoment v x (-w) := by
  unfold poissonLogMoment
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_nonneg
  intro j _
  have h1 := Real.add_one_le_exp (w j)
  have h2 := Real.add_one_le_exp (-(w j))
  simp only [Pi.neg_apply]
  nlinarith [hx j]

theorem sqrt_ratio_identity (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    p * (Real.sqrt q / Real.sqrt p - 1) + q * (Real.sqrt p / Real.sqrt q - 1) =
      -(Real.sqrt p - Real.sqrt q)^2 := by
  obtain ⟨a,ha,rfl⟩ : ∃ a, 0 < a ∧ p = a^2 :=
    ⟨Real.sqrt p,Real.sqrt_pos.mpr hp,(Real.sq_sqrt hp.le).symm⟩
  obtain ⟨b,hb,rfl⟩ : ∃ b, 0 < b ∧ q = b^2 :=
    ⟨Real.sqrt q,Real.sqrt_pos.mpr hq,(Real.sq_sqrt hq.le).symm⟩
  rw [Real.sqrt_sq ha.le,Real.sqrt_sq hb.le]
  field_simp
  ring

theorem poissonLogMoment_attained (v : E → J → ℝ) (x y : E)
    (hx : ∀ j, 0 < v x j) (hy : ∀ j, 0 < v y j) :
    ∃ β : J → ℝ, poissonLogMoment v x (-β) + poissonLogMoment v y β =
      -∑ j, (Real.sqrt (v x j) - Real.sqrt (v y j))^2 := by
  refine ⟨fun j => Real.log (Real.sqrt (v x j)) - Real.log (Real.sqrt (v y j)),?_⟩
  unfold poissonLogMoment
  rw [← Finset.sum_add_distrib,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have ex : Real.exp (Real.log (Real.sqrt (v x j))) = Real.sqrt (v x j) :=
    Real.exp_log (Real.sqrt_pos.mpr (hx j))
  have ey : Real.exp (Real.log (Real.sqrt (v y j))) = Real.sqrt (v y j) :=
    Real.exp_log (Real.sqrt_pos.mpr (hy j))
  simp only [Pi.neg_apply,neg_sub,Real.exp_sub,ex,ey]
  exact sqrt_ratio_identity _ _ (hx j) (hy j)

end Curvature

end ThresholdHC.PoissonComparison
