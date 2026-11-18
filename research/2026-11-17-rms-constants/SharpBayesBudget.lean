import SharpSmallPrefix
import ThresholdHC.Tier5.FiniteCreation
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Prod

/-! The finite-horizon risk-work inequality averaged over the uniform prior
and an arbitrary measurable seed and gap environment. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory Set Tier3 Tier5
open scoped unitInterval

private theorem integral_prior (f : ℝ → ℝ) :
    (∫ p : unitInterval, f p.val) = ∫ p in (0:ℝ)..1, f p := by
  rw [intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc,
    ← integral_subtype measurableSet_Icc]

private theorem prior_variance :
    (∫ p : unitInterval, p.val*(1-p.val)) = 1/6 := by
  rw [integral_prior (fun p => p*(1-p))]
  have hh (p : ℝ) : p*(1-p) = p-p^2 := by ring
  simp_rw [hh]
  have i₁ : IntervalIntegrable (fun p : ℝ => p) volume 0 1 := continuous_id.intervalIntegrable ..
  have i₂ : IntervalIntegrable (fun p : ℝ => p^2) volume 0 1 := (continuous_id.pow 2).intervalIntegrable ..
  rw [intervalIntegral.integral_sub i₁ i₂,integral_id,integral_pow]
  norm_num

def priorExpect {U : Type} {n : ℕ} (pol : U → List Bool → Option ℕ) (d : U → ℕ → ℝ)
    (F : unitInterval → U → Prefix n → ℝ) (z : unitInterval × U) :=
  ∑ w, creationLaw (pol z.2) (d z.2) (fun _ => z.1.val) w * F z.1 z.2 w

theorem measurable_priorExpect {U : Type} [MeasurableSpace U] {n : ℕ}
    (pol : U → List Bool → Option ℕ) (hp : MeasurableCreationPolicy pol)
    (d : U → ℕ → ℝ) (hd : MeasurableEnvironment d) (F : unitInterval → U → Prefix n → ℝ)
    (hm : ∀ w, Measurable (fun z : unitInterval × U => F z.1 z.2 w)) :
    Measurable (priorExpect pol d F) := by
  apply Finset.measurable_sum
  intro w _
  apply Measurable.mul _ (hm w)
  exact measurable_creationLaw (fun z : unitInterval × U => pol z.2)
    (fun xs a => measurable_snd (hp xs a)) (fun z => d z.2) (fun z _ => z.1.val)
    (fun i => (hd i).comp measurable_snd) (fun _ => measurable_subtype_coe.comp measurable_fst) w

theorem priorExpect_bound {U : Type} {n : ℕ} (pol : U → List Bool → Option ℕ)
    (d : U → ℕ → ℝ) (hd : ∀ u i, 0 ≤ d u i ∧ d u i ≤ 1/2)
    (F : unitInterval → U → Prefix n → ℝ) (C : ℝ) (hb : ∀ p u w, |F p u w| ≤ C)
    (z : unitInterval × U) : |priorExpect pol d F z| ≤ C := by
  have hp := creationLaw_total n (pol z.2) (d z.2) (fun _ => z.1.val) (hd z.2) (fun _ => z.1.property)
  apply (Finset.abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ w : Prefix n, creationLaw (pol z.2) (d z.2) (fun _ => z.1.val) w * C := by
      apply Finset.sum_le_sum
      intro w _
      rw [abs_mul,abs_of_nonneg (hp.1 w)]
      exact mul_le_mul_of_nonneg_left (hb ..) (hp.1 w)
    _ = C := by rw [← Finset.sum_mul,hp.2,one_mul]

private theorem loss_bound (x p : ℝ) (hx : x ∈ Icc 0 1) (hp : p ∈ Icc 0 1) :
    |(x-p)^2| ≤ 1 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [mul_nonneg (show 0 ≤ 1-x+p by linarith [hx.2,hp.1])
    (show 0 ≤ 1+x-p by linarith [hx.1,hp.2])]

theorem four_budget_prefix_bayes {U : Type} [MeasurableSpace U] (ν : Measure U)
    [IsProbabilityMeasure ν] {n : ℕ} (pol : U → List Bool → Option ℕ)
    (hp : MeasurableCreationPolicy pol) (d : U → ℕ → ℝ) (hm : MeasurableEnvironment d)
    (hd : ∀ u i, 0 ≤ d u i ∧ d u i ≤ 1/2)
    (X : U → Prefix n → ℝ) (hX : ∀ w, Measurable (fun u => X u w))
    (hXb : ∀ u w, X u w ∈ Icc 0 1)
    (hwork : ∀ p : unitInterval, (∫ u, priorExpect pol d (fun _ _ => @workOf n) (p,u) ∂ν) ≤ 4) :
    (1/36:ℝ) ≤ ∫ p : unitInterval, ∫ u,
      priorExpect pol d (fun q v w => (X v w-q.val)^2) (p,u) ∂ν := by
  let L := priorExpect pol d (fun (p : unitInterval) u w => (X u w-p.val)^2)
  let W := priorExpect pol d (fun _ _ => @workOf n)
  let v := fun p : unitInterval => p.val*(1-p.val)
  let G := fun z : unitInterval × U => L z -(10-W z)/36*v z.1
  have hLm : Measurable L := measurable_priorExpect pol hp d hm _ (fun w =>
    (((hX w).comp measurable_snd).sub (measurable_subtype_coe.comp measurable_fst)).pow_const 2)
  have hWm : Measurable W := measurable_priorExpect pol hp d hm _ (fun _ => measurable_const)
  have hvm : Measurable v := measurable_subtype_coe.mul (measurable_const.sub measurable_subtype_coe)
  have hGm : Measurable G := hLm.sub (((measurable_const.sub hWm).div_const 36).mul (hvm.comp measurable_fst))
  have hL (z) : |L z| ≤ 1 := priorExpect_bound pol d hd _ 1 (fun p u w => loss_bound _ _ (hXb u w) p.property) z
  have hW (z) : |W z| ≤ n := priorExpect_bound pol d hd _ n (fun _ _ w => by
    rw [abs_of_nonneg (workOf_nonneg _)]; exact workOf_le_length _) z
  have hv (p) : 0 ≤ v p ∧ v p ≤ 1 := by
    constructor
    · exact mul_nonneg p.property.1 (sub_nonneg.mpr p.property.2)
    · dsimp [v]
      nlinarith [p.property.2,sq_nonneg p.val]
  have hGi : Integrable G (volume.prod ν) := by
    apply (integrable_const (1+(10+(n:ℝ))/36)).mono' hGm.aestronglyMeasurable
    apply ae_of_all
    intro z
    change |L z-(10-W z)/36*v z.1| ≤ _
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_div,abs_of_nonneg (hv z.1).1,abs_of_pos (by norm_num : (0:ℝ)<36)]
    have hdiff : |10-W z| ≤ 10+n := (abs_sub ..).trans (by rw [abs_of_pos (by norm_num : (0:ℝ)<10)]; linarith [hW z])
    exact add_le_add (hL z) ((mul_le_mul_of_nonneg_left (hv z.1).2 (by positivity)).trans (by linarith))
  have hG (u : U) : 0 ≤ ∫ p : unitInterval, G (p,u) := by
    let P := fun (p : ℝ) (w : Prefix n) => creationLaw (pol u) (d u) (fun _=>p) w
    let term := fun (p : ℝ) (w : Prefix n) => P p w*((X u w-p)^2-(10-workOf w)/36*(p*(1-p)))
    have eqG (p : unitInterval) : G (p,u) = ∑ w, term p.val w := by
      have ht := (creationLaw_total n (pol u) (d u) (fun _=>p.val) (hd u) (fun _=>p.property)).2
      change ∑ w, P p.val w = 1 at ht
      simp only [G,L,W,v,priorExpect,term, mul_sub (P _ _) ((_ - _)^2),Finset.sum_sub_distrib]
      change (∑ w, P p.val w * _) - _ = (∑ w, P p.val w * _) - _
      congr 1
      calc
        _ = (10*(∑ w, P p.val w) - ∑ w, P p.val w*workOf w)/36*(p.val*(1-p.val)) := by rw [ht]; ring
        _ = _ := by
          rw [Finset.mul_sum,← Finset.sum_sub_distrib,Finset.sum_div,Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro w _
          ring
    have htmeas (w : Prefix n) : Measurable (fun p : unitInterval => term p.val w) := by
      have hP := measurable_creationLaw (Seed := unitInterval) (fun _ => pol u)
        (fun _ _ => measurableSet_eq_fun measurable_const measurable_const)
        (fun _ => d u) (fun p _ => p.val) (fun _ => measurable_const) (fun _ => measurable_subtype_coe) w
      dsimp only [term,P]
      exact hP.mul (by fun_prop)
    have htint (w : Prefix n) : Integrable (fun p : unitInterval => term p.val w) volume := by
      apply (integrable_const (1+(10+(n:ℝ))/36)).mono' (htmeas w).aestronglyMeasurable
      apply ae_of_all
      intro p
      have hpr := creationLaw_total n (pol u) (d u) (fun _=>p.val) (hd u) (fun _=>p.property)
      have hP1 : P p.val w ≤ 1 := (Finset.single_le_sum (fun i _ => hpr.1 i) (Finset.mem_univ w)).trans_eq hpr.2
      change |P p.val w * _| ≤ _
      rw [abs_mul,abs_of_nonneg (hpr.1 w)]
      apply (mul_le_mul_of_nonneg_right hP1 (abs_nonneg _)).trans
      rw [one_mul]
      apply (abs_sub _ _).trans
      rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<36),abs_of_nonneg (hv p).1]
      have hdiff : |10-workOf w| ≤ 10+n := (abs_sub ..).trans (by
        rw [abs_of_pos (by norm_num : (0:ℝ)<10),abs_of_nonneg (workOf_nonneg _)]; linarith [workOf_le_length w])
      exact add_le_add (loss_bound _ _ (hXb u w) p.property)
        ((mul_le_mul_of_nonneg_left (hv p).2 (by positivity)).trans (by linarith))
    simp_rw [eqG]
    rw [integral_finsetSum _ (fun w _ => htint w)]
    apply Finset.sum_nonneg
    intro w _
    rw [integral_prior (fun p => term p w)]
    exact creation_leaf_risk_work (pol u) (d u) (hd u) w (X u w)
  have hi : 0 ≤ ∫ p : unitInterval, ∫ u, G (p,u) ∂ν := by
    rw [integral_integral_swap (f := fun p u => G (p,u)) hGi]
    exact integral_nonneg hG
  have hLi : Integrable L (volume.prod ν) :=
    (integrable_const _).mono' hLm.aestronglyMeasurable (ae_of_all _ hL)
  have hvi : Integrable v volume := (integrable_const (1:ℝ)).mono' hvm.aestronglyMeasurable
    (ae_of_all _ fun p => by rw [Real.norm_eq_abs,abs_of_nonneg (hv p).1]; exact (hv p).2)
  have hpwise (p : unitInterval) : (∫ u, G (p,u) ∂ν) ≤ (∫ u, L (p,u) ∂ν) - (1/6)*v p := by
    have wI : Integrable (fun u => W (p,u)) ν := (integrable_const (n:ℝ)).mono'
      (hWm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (ae_of_all _ fun u => hW _)
    have lI : Integrable (fun u => L (p,u)) ν := (integrable_const (1:ℝ)).mono'
      (hLm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (ae_of_all _ fun u => hL _)
    have e (u : U) : G (p,u) = L (p,u) - (10-W (p,u))*(v p/36) := by dsimp [G]; ring
    simp_rw [e]
    have subI : Integrable (fun u => 10-W (p,u)) ν := (integrable_const (10:ℝ)).sub wI
    rw [integral_sub lI (subI.mul_const _),integral_mul_const,integral_sub (integrable_const (10:ℝ)) wI]
    simp only [integral_const,probReal_univ,one_smul]
    linarith only [mul_nonneg (show 0 ≤ 4-(∫ u, W (p,u) ∂ν) by linarith [hwork p]) (hv p).1]
  have up := integral_mono hGi.integral_prod_left (hLi.integral_prod_left.sub (hvi.const_mul (1/6))) hpwise
  change _ ≤ ∫ p : unitInterval, (∫ u, L (p,u) ∂ν)-(1/6)*v p at up
  rw [integral_sub hLi.integral_prod_left (hvi.const_mul _),integral_const_mul,prior_variance] at up
  change _ ≤ ∫ p : unitInterval, ∫ u, L (p,u) ∂ν
  linarith only [hi,up]

end ThresholdHC.SharpRMS
