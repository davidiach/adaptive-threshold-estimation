import ThresholdHC.PoissonComparison.Law
import ThresholdHC.CriticalEntropy.FiniteAffinity

/-! The Hellinger affinity of two Poisson vector laws with positive
intensities, `exp (-(∑ j, (sqrt (w j) - sqrt (w' j))^2)/2)` (the formula of
`lem:comparison` for Poisson vectors). The law with intensities `w'` has
density `exp (2 L)` with respect to the law with intensities `w`, where `L`
is half the log-likelihood ratio, an affine score in the counts; the affinity
is then the exponential moment of `L`. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Nat ENNReal
namespace ThresholdHC.PoissonComparison
open ThresholdHC.CriticalEntropy

/-- Half the log-likelihood ratio `log (dP_{w'}/dP_w)/2`, affine in the counts. -/
def halfLogRatio {J : Type} [Fintype J] (w w' : J → ℝ) (z : J → ℕ) : ℝ :=
  ∑ j, (w j - w' j)/2 +
    ∑ j, (Real.log (Real.sqrt (w' j)) - Real.log (Real.sqrt (w j))) * (z j : ℝ)

theorem poisson_density_factor (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (n : ℕ) :
    Real.exp (2*((p-q)/2+(Real.log (Real.sqrt q)-Real.log (Real.sqrt p))*n)) *
      (Real.exp (-p)*p^n/(n)!) = Real.exp (-q)*q^n/(n)! := by
  have ht : Real.exp (Real.log (Real.sqrt q)-Real.log (Real.sqrt p)) =
      Real.sqrt q/Real.sqrt p := by
    rw [Real.exp_sub,Real.exp_log (Real.sqrt_pos.mpr hq),Real.exp_log (Real.sqrt_pos.mpr hp)]
  have h2 : 2*((p-q)/2+(Real.log (Real.sqrt q)-Real.log (Real.sqrt p))*n) =
      (p-q)+((2*n : ℕ) : ℝ)*(Real.log (Real.sqrt q)-Real.log (Real.sqrt p)) := by
    push_cast
    ring
  rw [h2,Real.exp_add,Real.exp_nat_mul,ht,pow_mul,div_pow,Real.sq_sqrt hq.le,
    Real.sq_sqrt hp.le,div_pow]
  have hpn : p^n ≠ 0 := pow_ne_zero _ hp.ne'
  have he : Real.exp (p-q)*Real.exp (-p) = Real.exp (-q) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (p-q)*Real.exp (-p))*(q^n/p^n*p^n)/(n)! := by ring
    _ = _ := by rw [he,div_mul_cancel₀ _ hpn]

theorem poissonVectorLaw_eq_withDensity {J : Type} [Fintype J] (w w' : J → ℝ)
    (hw : ∀ j, 0 < w j) (hw' : ∀ j, 0 < w' j) :
    poissonVectorLaw w' = (poissonVectorLaw w).withDensity
      (fun z => ENNReal.ofReal (Real.exp (2*halfLogRatio w w' z))) := by
  have hm : ∀ (u : J → ℝ), (∀ j, 0 < u j) → ∀ (z : J → ℕ) (j : J),
      0 ≤ Real.exp (-u j)*u j^(z j)/(z j)! := fun u hu z j =>
    div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (hu j).le _)) (Nat.cast_nonneg _)
  apply Measure.ext_of_singleton
  intro z
  rw [withDensity_apply _ (measurableSet_singleton z),lintegral_singleton,
    poissonVectorLaw_singleton w (fun j => (hw j).le),
    poissonVectorLaw_singleton w' (fun j => (hw' j).le),
    ← ENNReal.ofReal_prod_of_nonneg (fun j _ => hm w hw z j),
    ← ENNReal.ofReal_prod_of_nonneg (fun j _ => hm w' hw' z j),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  have hL : Real.exp (2*halfLogRatio w w' z) = ∏ j, Real.exp (2*((w j-w' j)/2+
      (Real.log (Real.sqrt (w' j))-Real.log (Real.sqrt (w j)))*(z j))) := by
    rw [← Real.exp_sum]
    congr 1
    unfold halfLogRatio
    rw [← Finset.sum_add_distrib,Finset.mul_sum]
  rw [hL,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  exact (poisson_density_factor _ _ (hw j) (hw' j) (z j)).symm

theorem sqrt_affinity_identity (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (p-q)/2+p*(Real.sqrt q/Real.sqrt p-1) = -((Real.sqrt p-Real.sqrt q)^2/2) := by
  obtain ⟨a,ha,rfl⟩ : ∃ a, 0 < a ∧ p = a^2 :=
    ⟨Real.sqrt p,Real.sqrt_pos.mpr hp,(Real.sq_sqrt hp.le).symm⟩
  obtain ⟨b,hb,rfl⟩ : ∃ b, 0 < b ∧ q = b^2 :=
    ⟨Real.sqrt q,Real.sqrt_pos.mpr hq,(Real.sq_sqrt hq.le).symm⟩
  rw [Real.sqrt_sq ha.le,Real.sqrt_sq hb.le]
  field_simp
  ring

/-- The Hellinger affinity of two Poisson vector laws with positive intensities. -/
theorem poissonVectorLaw_affinity {J : Type} [Fintype J] (w w' : J → ℝ)
    (hw : ∀ j, 0 < w j) (hw' : ∀ j, 0 < w' j) :
    (hellingerAffinity (poissonVectorLaw w) (poissonVectorLaw w')).toReal =
      Real.exp (-(∑ j, (Real.sqrt (w j) - Real.sqrt (w' j))^2)/2) := by
  set ρ : (J → ℕ) → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (2*halfLogRatio w w' z))
    with hρ
  have hdens := poissonVectorLaw_eq_withDensity w w' hw hw'
  have h1 : hellingerAffinity (poissonVectorLaw w) (poissonVectorLaw w') =
      hellingerAffinity ((poissonVectorLaw w).withDensity 1)
        ((poissonVectorLaw w).withDensity ρ) := by
    rw [withDensity_one,← hdens]
  rw [h1,hellingerAffinity_withDensity_nonnegative _ 1 ρ (measurable_of_countable _)
    (measurable_of_countable _) (fun _ => ENNReal.one_ne_top) (fun _ => ENNReal.ofReal_ne_top)]
  have h2 : (fun z => ((1 : (J → ℕ) → ℝ≥0∞) z*ρ z)^(1/2 : ℝ)) =
      (fun z => ENNReal.ofReal (Real.exp (∑ j, (w j-w' j)/2 +
        ∑ j, (Real.log (Real.sqrt (w' j))-Real.log (Real.sqrt (w j)))*(z j : ℝ)))) := by
    funext z
    rw [Pi.one_apply,one_mul,hρ,ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le
      (by norm_num),← Real.exp_mul]
    congr 2
    unfold halfLogRatio
    ring
  rw [h2,← ofReal_integral_eq_lintegral_ofReal (poissonVectorLaw_exp_integrable _ _ _)
    (Filter.Eventually.of_forall (fun z => (Real.exp_pos _).le)),
    poissonVectorLaw_exp_integral _ (fun j => (hw j).le),
    ENNReal.toReal_ofReal (Real.exp_pos _).le,← Finset.sum_add_distrib,neg_div,Finset.sum_div,
    ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.exp_sub,Real.exp_log (Real.sqrt_pos.mpr (hw' j)),
    Real.exp_log (Real.sqrt_pos.mpr (hw j))]
  exact sqrt_affinity_identity _ _ (hw j) (hw' j)

end ThresholdHC.PoissonComparison
