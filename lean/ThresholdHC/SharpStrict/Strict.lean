import ThresholdHC.SharpStrict.Specification
import ThresholdHC.SharpRMS.OracleBounds

/-! Strictness of the sharp universal RMS lower bound for every budget other
than four. The argument reruns the transfer steps of the SharpRMS group with
an explicit slack: the prefix Bayes transfer with an arbitrary constant, the
small-budget risk-work inequality with work at most B, the tapered-price and
rectangle transfers with an integral cap below 4/3, a strict cover of the
certified window and a strict near-perfect integral. -/
noncomputable section
namespace ThresholdHC.SharpStrict
open MeasureTheory Set Filter Tier3 Tier4 Tier5 Tier6 OracleLower
open ThresholdHC.SharpRMS ThresholdHC.SharpRMS.Window
open scoped ENNReal Topology unitInterval

/-! ### Prefix Bayes transfer with an arbitrary constant -/

private def flatPrior (p : unitInterval) : SignLaw :=
  ⟨fun _ => p.val, measurable_const, fun _ => p.property⟩

/-- A finite-prefix Bayes lower bound c², uniform in the horizon, passes to
the population minimax risk as the lower bound c. -/
theorem minimax_from_prefix_bayes_const (μ : Measure Gap) [IsProbabilityMeasure μ] (B c : ℝ)
    (priorBound : ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R), UniformBudget μ A B →
      ∀ n (X : PopulationSeed R → Prefix n → ℝ), (∀ w, Measurable (fun u => X u w)) →
      (∀ u w, X u w ∈ Icc 0 1) → c^2 ≤ ∫ p : unitInterval, ∫ u,
        priorExpect (populationPolicy A) populationGap (fun q v w => (X v w-q.val)^2) (p,u)
          ∂populationSeedLaw μ A) : ENNReal.ofReal c ≤ minimaxRisk μ B := by
  apply le_sInf
  rintro _ ⟨R,mR,A,hb,rfl⟩
  by_contra! hsmall
  let r := (maximalRMSRisk μ A).toReal
  have hr : ENNReal.ofReal r = maximalRMSRisk μ A := ENNReal.ofReal_toReal
    (hsmall.trans ENNReal.ofReal_lt_top).ne
  have hr' : r < c := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mp (hr.trans_lt hsmall)
  let Y := fun z : PopulationSeed R × ProcessTape => max 0 (min 1 (populationOutput A z))
  have hYm : Measurable Y := measurable_const.max (measurable_const.min (measurable_populationOutput A))
  have hY (z) : Y z ∈ Icc 0 1 := ⟨le_max_left ..,max_le (by norm_num) (min_le_left ..)⟩
  let P := fun p : unitInterval => experimentLaw μ A (flatPrior p)
  let f := fun (p : unitInterval) z => (Y z - p.val)^2
  have fm p : Measurable (f p) := (hYm.sub measurable_const).pow_const 2
  have bound (x : ℝ) (hx : x ∈ Icc 0 1) (p : unitInterval) : |(x-p.val)^2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [mul_nonneg (show 0 ≤ 1-x+p.val by linarith [hx.2,p.property.1])
      (show 0 ≤ 1+x-p.val by linarith [hx.1,p.property.2])]
  have integr (p) : Integrable (f p) (P p) :=
    (integrable_const (1:ℝ)).mono' (fm p).aestronglyMeasurable (ae_of_all _ fun z => bound _ (hY z) p)
  let risk := fun p : unitInterval => ∫ z, f p z ∂P p
  have risk_le (p : unitInterval) : risk p ≤ r^2 := by
    have ht : signMean μ (flatPrior p).val = p.val := by simp [signMean,flatPrior]
    have root := le_iSup (fun q => rootMeanRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val)) (flatPrior p)
    change _ ≤ maximalRMSRisk μ A at root
    rw [ht,← hr] at root
    have sq : squaredRisk (P p) (populationOutput A) p.val ≤ ENNReal.ofReal (r^2) := by
      by_contra! bad
      have hh := ENNReal.rpow_lt_rpow bad (by norm_num : (0:ℝ)<1/2)
      rw [ofReal_square_rpow_half r ENNReal.toReal_nonneg] at hh
      exact (not_lt_of_ge root) hh
    apply (ENNReal.ofReal_le_ofReal_iff (sq_nonneg r)).mp
    apply le_trans _ sq
    rw [show ENNReal.ofReal (risk p) = ∫⁻ z, ENNReal.ofReal (f p z) ∂P p from
      ofReal_integral_eq_lintegral_ofReal (integr p) (ae_of_all _ fun _ => sq_nonneg _)]
    apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    let y := populationOutput A z
    change (max 0 (min 1 y)-p.val)^2 ≤ (y-p.val)^2
    rcases le_total y 0 with hy | hy
    · rw [min_eq_right (by linarith),max_eq_left hy]
      nlinarith [mul_nonneg (neg_nonneg.mpr hy) (show 0 ≤ 2*p.val-y by linarith [p.property.1])]
    · rcases le_total y 1 with h' | h'
      · rw [min_eq_right h',max_eq_right hy]
      · rw [min_eq_left h',max_eq_right (by norm_num)]
        nlinarith [mul_nonneg (sub_nonneg.mpr h') (show 0 ≤ y+1-2*p.val by linarith [p.property.2])]
  let ν := populationSeedLaw μ A
  let F := fun (n : ℕ) (u : PopulationSeed R) (w : Prefix n) => Y (padJoint n (u,w))
  have Fm (n : ℕ) (w : Prefix n) : Measurable (fun u => F n u w) :=
    (hYm.comp (measurable_padJoint n)).comp (measurable_id.prodMk measurable_const)
  let L := fun n => priorExpect (populationPolicy A) populationGap
    (fun p u w => (F n u w-p.val)^2)
  let N := fun n (p : unitInterval) => ∫ u, L n (p,u) ∂ν
  have eqn (n) (p : unitInterval) : (∫ z, f p (observePrefix n z) ∂P p) = N n p :=
    (population_realization R μ A (flatPrior p)).2 n (fun u w => (F n u w-p.val)^2)
      (fun w => ((Fm n w).sub measurable_const).pow_const 2) ⟨1,fun u w => bound _ (hY _) p⟩
  have avg (n : ℕ) : c^2 ≤ ∫ p : unitInterval, N n p := priorBound R A hb n (F n) (Fm n) (fun _ _ => hY _)
  have lim (p : unitInterval) : Tendsto (fun n => N n p) atTop (𝓝 (risk p)) :=
    (limit_prefix A μ (flatPrior p) B hb (f p) (fm p) 1 (fun z => bound _ (hY z) p)).congr (fun n => eqn n p)
  have hLm (n : ℕ) : Measurable (L n) := measurable_priorExpect (populationPolicy A)
    (measurable_populationPolicy A) populationGap measurable_populationGap _
    (fun w => (((Fm n w).comp measurable_snd).sub (measurable_subtype_coe.comp measurable_fst)).pow_const 2)
  have hNb (n : ℕ) (p : unitInterval) : ‖N n p‖ ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun u => L n (p,u))
      (ae_of_all _ fun u => priorExpect_bound (populationPolicy A) populationGap
        (fun u i => ⟨(u.2 i).property.1.le,(u.2 i).property.2⟩) _ 1 (fun p u w => bound _ (hY _) p) (p,u))
    simpa using this
  have Nm n : AEStronglyMeasurable (N n) volume := (hLm n).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have limAvg := tendsto_integral_of_dominated_convergence (μ := (volume : Measure unitInterval))
    (fun _ => (1:ℝ)) Nm (integrable_const 1) (fun n => ae_of_all _ (hNb n)) (ae_of_all _ lim)
  have low := ge_of_tendsto limAvg (Eventually.of_forall avg)
  have hi : Integrable risk volume := (integrable_const (1:ℝ)).mono'
    (aestronglyMeasurable_of_tendsto_ae atTop Nm (ae_of_all _ lim))
    (ae_of_all _ fun p => le_of_tendsto (lim p).norm (Eventually.of_forall fun n => hNb n p))
  have up := integral_mono hi (integrable_const (r^2)) risk_le
  simp only [integral_const,probReal_univ,one_smul] at up
  nlinarith only [low,up,mul_pos (show 0 < c-r by linarith) (show 0 < c+r by
    have := show 0 ≤ r from ENNReal.toReal_nonneg; linarith)]

/-! ### Small budgets: the risk-work inequality with work at most B -/

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

private theorem loss_bound (x p : ℝ) (hx : x ∈ Icc 0 1) (hp : p ∈ Icc 0 1) :
    |(x-p)^2| ≤ 1 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [mul_nonneg (show 0 ≤ 1-x+p by linarith [hx.2,hp.1])
    (show 0 ≤ 1+x-p by linarith [hx.1,hp.2])]

/-- The uniform-prior Bayes risk of a finite prefix with expected work at
most B is at least (10-B)/216. -/
theorem budget_prefix_bayes {U : Type} [MeasurableSpace U] (ν : Measure U)
    [IsProbabilityMeasure ν] {n : ℕ} (pol : U → List Bool → Option ℕ)
    (hp : MeasurableCreationPolicy pol) (d : U → ℕ → ℝ) (hm : MeasurableEnvironment d)
    (hd : ∀ u i, 0 ≤ d u i ∧ d u i ≤ 1/2)
    (X : U → Prefix n → ℝ) (hX : ∀ w, Measurable (fun u => X u w))
    (hXb : ∀ u w, X u w ∈ Icc 0 1) (B : ℝ)
    (hwork : ∀ p : unitInterval, (∫ u, priorExpect pol d (fun _ _ => @workOf n) (p,u) ∂ν) ≤ B) :
    (10-B)/216 ≤ ∫ p : unitInterval, ∫ u,
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
  have hpwise (p : unitInterval) : (∫ u, G (p,u) ∂ν) ≤ (∫ u, L (p,u) ∂ν) - ((10-B)/36)*v p := by
    have wI : Integrable (fun u => W (p,u)) ν := (integrable_const (n:ℝ)).mono'
      (hWm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (ae_of_all _ fun u => hW _)
    have lI : Integrable (fun u => L (p,u)) ν := (integrable_const (1:ℝ)).mono'
      (hLm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (ae_of_all _ fun u => hL _)
    have e (u : U) : G (p,u) = L (p,u) - (10-W (p,u))*(v p/36) := by dsimp [G]; ring
    simp_rw [e]
    have subI : Integrable (fun u => 10-W (p,u)) ν := (integrable_const (10:ℝ)).sub wI
    rw [integral_sub lI (subI.mul_const _),integral_mul_const,integral_sub (integrable_const (10:ℝ)) wI]
    simp only [integral_const,probReal_univ,one_smul]
    linarith only [mul_nonneg (show 0 ≤ B-(∫ u, W (p,u) ∂ν) by linarith [hwork p]) (hv p).1]
  have up := integral_mono hGi.integral_prod_left (hLi.integral_prod_left.sub (hvi.const_mul ((10-B)/36))) hpwise
  change _ ≤ ∫ p : unitInterval, (∫ u, L (p,u) ∂ν)-((10-B)/36)*v p at up
  rw [integral_sub hLi.integral_prod_left (hvi.const_mul _),integral_const_mul,prior_variance] at up
  change _ ≤ ∫ p : unitInterval, ∫ u, L (p,u) ∂ν
  linarith only [hi,up]

/-- With at most `B ≤ 10` expected flips, the minimax RMS risk of every gap law is
at least `√((10 - B)/216)`; policies may use private randomness and unbounded
stopping. -/
theorem small_budget_minimax_lower (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ)
    (hB : 0 ≤ B) (hten : B ≤ 10) : ENNReal.ofReal (Real.sqrt ((10-B)/216)) ≤ minimaxRisk μ B := by
  apply minimax_from_prefix_bayes_const μ B
  intro R _ A hb n X hm hX
  rw [Real.sq_sqrt (by linarith)]
  exact budget_prefix_bayes (populationSeedLaw μ A) (populationPolicy A) (measurable_populationPolicy A)
    populationGap measurable_populationGap (fun u i => ⟨(u.2 i).property.1.le,(u.2 i).property.2⟩)
    X hm hX B (fun p => population_prefix_work_budget μ A B hB hb n p)

/-! ### Tapered prices with an integral cap below 4/3 -/

private theorem uniform_transform (f : ℝ → ℝ) :
    2*(∫ p : unitInterval, f (2*p.val-1)) = ∫ t in (-1:ℝ)..1, f t := by
  have eqI : (∫ p : unitInterval, f (2*p.val-1)) = ∫ p in (0:ℝ)..1, f (2*p-1) := by
    rw [intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc,← integral_subtype measurableSet_Icc]
  rw [eqI]
  simpa only [smul_eq_mul, mul_zero,zero_add,mul_one,show (2:ℝ)+(-1)=1 by norm_num,sub_eq_add_neg] using
    intervalIntegral.smul_integral_comp_mul_add (a := (0:ℝ)) (b := 1) f 2 (-1)

private theorem finite_critical_tradeoff {n : ℕ} (pol : List Bool → Option ℕ) (s : ℝ)
    (hs : 0 < s) (hs' : s < 1) (X : Prefix n → ℝ) (K : ℝ → ℝ)
    (hK : IntervalIntegrable K volume (-1) 1)
    (hprice : ∀ t, |t| < 1 → ∃ P, 0 < P ∧ P ≤ 1 ∧ admissibleExitPrice s |t| P ∧
      (1-t^2)^2 ≤ K t*P) :
    let Q := fun (p : unitInterval) (w : Prefix n) => creationLaw pol (fun _=>s/2) (fun _=>p.val) w
    (20/3:ℝ) ≤ 144*(∫ p : unitInterval, ∑ w, Q p w*(X w-p.val)^2) +
      ∫ p : unitInterval, s^2*K (2*p.val-1)*(∑ w, Q p w*workOf w) := by
  let F := fun (w : Prefix n) (t : ℝ) => creationLaw pol (fun _=>s/2) (fun _=>(1+t)/2) w
  let D := fun w => deriv (F w)
  let W := fun t => ∑ w, F w t*workOf w
  let J := fun t => ∑ w, (D w t)^2/F w t
  let p := creationLaw (n := n) pol (fun _=>s/2) (fun _=>1/2)
  let z := fun w : Prefix n => posterior (capPolicy (coinCap n pol) pol) w (fun _=>s/2)
  have tilt (w) : F w = fun t => tiltedMass p z t w := by
    funext t
    exact creation_tilt pol w _ (fun _=>t) (fun _=>⟨by linarith,by linarith⟩)
  have smooth (w) : ContDiff ℝ 1 (F w) := by rw [tilt]; unfold tiltedMass; fun_prop
  have fc w := (smooth w).continuous
  have dc w : Continuous (D w) := (contDiff_one_iff_deriv.mp (smooth w)).2
  have diff w t : HasDerivAt (F w) (D w t) t := ((smooth w).differentiable (by norm_num) t).hasDerivAt
  have cW : Continuous W := by dsimp [W]; fun_prop
  have prob t (ht : t ∈ Icc (-1:ℝ) 1) := creationLaw_total n pol (fun _=>s/2) (fun _=>(1+t)/2)
    (fun _=>⟨by linarith,by linarith⟩) (fun _=>⟨by linarith [ht.1],by linarith [ht.2]⟩)
  have regular (w) (t) (ht : t ∈ Ioo (-1:ℝ) 1) : 0 ≤ F w t ∧ (F w t = 0 → D w t = 0) := by
    refine ⟨(prob t ⟨ht.1.le,ht.2.le⟩).1 w,?_⟩
    intro zero
    have hprod : ∀ i, |z w i| ≤ 1 := by
      intro i
      let a := Proofs.coinLike (capPolicy (coinCap n pol) pol) w i (1/2+s/2)
      let b := Proofs.coinLike (capPolicy (coinCap n pol) pol) w i (1/2-s/2)
      have ha : 0 ≤ a := Proofs.coinLike_nonneg _ _ _ (by linarith) (by linarith)
      have hb : 0 ≤ b := Proofs.coinLike_nonneg _ _ _ (by linarith) (by linarith)
      change |(a-b)/(a+b)| ≤ 1
      by_cases hz : a+b=0
      · simp [hz]
      · rw [abs_div,abs_of_nonneg (add_nonneg ha hb),div_le_one (lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hz)),abs_le]
        constructor <;> linarith
    have hh (i) : 0 < 1+t*z w i := by
      have hl : |t*z w i| < 1 := by rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hprod i) (abs_nonneg t)).trans_lt (by simpa using abs_lt.mpr ht)
      linarith [(abs_lt.mp hl).1]
    rw [tilt] at zero
    have hzero : p w = 0 := (mul_eq_zero.mp zero).resolve_right (Finset.prod_ne_zero_iff.mpr fun i _ => (hh i).ne')
    dsimp [D]
    rw [tilt]
    simp [tiltedMass,hzero]
  have hki : IntervalIntegrable (fun t => s^2*K t*W t) volume (-1) 1 :=
    (hK.const_mul _).mul_continuousOn cW.continuousOn
  have price (t : ℝ) (ht : t ∈ Ioo (-1:ℝ) 1) : (1-t^2)^2*J t ≤ s^2*K t*W t := by
    obtain ⟨P,hp,hp',hex,hcomp⟩ := hprice t (abs_lt.mpr ht)
    have ha := adaptive_fisher_price (n := n) pol s t P hs hs' (abs_lt.mpr ht) hp' hex
    change P*J t ≤ s^2*W t at ha
    have hJ : 0 ≤ J t := Finset.sum_nonneg fun w _ => div_nonneg (sq_nonneg _) (regular w t ht).1
    have hn : 0 ≤ K t := by by_contra! hx; linarith [mul_neg_of_neg_of_pos hx hp,sq_nonneg (1-t^2)]
    linarith only [mul_le_mul_of_nonneg_right hcomp hJ,mul_le_mul_of_nonneg_left ha hn]
  have bound := finite_score_tradeoff F D (fun w=>2*X w-1) regular dc diff
    (fun t ht => (prob t ht).2) _ hki price
  rw [← uniform_transform,← uniform_transform] at bound
  let Q := fun (p : unitInterval) (w : Prefix n) => creationLaw pol (fun _=>s/2) (fun _=>p.val) w
  have eqF (p : unitInterval) (w) : F w (2*p.val-1)=Q p w := by
    unfold F Q
    rw [show (1+(2*p.val-1))/2 = p.val by ring]
  have loss (p : unitInterval) : (∑ w, F w (2*p.val-1)*(2*X w-1-(2*p.val-1))^2) =
      4*∑ w, Q p w*(X w-p.val)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [eqF]
    ring
  simp_rw [loss,integral_const_mul] at bound
  simp only [W,eqF] at bound
  linarith only [bound]

/-- The tapered-price transfer with the integral cap a in place of 4/3: the
critical single-gap minimax risk is at least the square root of
(20/3-2a)/144, which exceeds one sixth when a is below 4/3. -/
theorem minimax_from_tapered_price_slack (g : Gap) (B : ℝ) (hg : 2*g.val < 1)
    (hbudget : (2*g.val)^2*B=4) (K : ℝ → ℝ) (hm : Measurable K)
    (hK : IntervalIntegrable K volume (-1) 1)
    (hcap : ∃ C : ℝ, ∀ t ∈ Icc (-1:ℝ) 1, 0 ≤ K t ∧ K t ≤ C) (a : ℝ) (ha : a ≤ 10/3)
    (havg : (∫ t in (-1:ℝ)..1, K t) ≤ a)
    (hprice : ∀ t, |t| < 1 → ∃ P, 0 < P ∧ P ≤ 1 ∧ admissibleExitPrice (2*g.val) |t| P ∧
      (1-t^2)^2 ≤ K t*P) :
    ENNReal.ofReal (Real.sqrt ((20/3-2*a)/144)) ≤ minimaxRisk (Measure.dirac g) B := by
  let s := 2*g.val
  have hs : 0 < s := by dsimp [s]; linarith [g.property.1]
  have hB : 0 ≤ B := by by_contra! hh; linarith [mul_neg_of_pos_of_neg (sq_pos_of_pos hs) hh]
  obtain ⟨C,cap⟩ := hcap
  let V := fun p : unitInterval => K (2*p.val-1)
  have vt p : 2*(p:unitInterval).val-1 ∈ Icc (-1:ℝ) 1 := ⟨by linarith [p.property.1],by linarith [p.property.2]⟩
  have vb (p : unitInterval) : 0 ≤ V p ∧ V p ≤ C := cap _ (vt p)
  have vm : Measurable V := hm.comp ((measurable_const.mul measurable_subtype_coe).sub measurable_const)
  have vi : Integrable V volume := (integrable_const C).mono' vm.aestronglyMeasurable
    (ae_of_all _ fun p => by rw [Real.norm_eq_abs,abs_of_nonneg (vb p).1]; exact (vb p).2)
  have vavg : (∫ p : unitInterval, V p) ≤ a/2 := by linarith only [uniform_transform K,havg]
  apply minimax_from_prefix_bayes_const _ B
  intro R _ A hb n X hX hXb
  rw [Real.sq_sqrt (by linarith)]
  let ν := populationSeedLaw (Measure.dirac g) A
  let pol := populationPolicy A
  let L := priorExpect pol populationGap (fun (p : unitInterval) u w => (X u w-p.val)^2)
  let W := priorExpect pol populationGap (fun _ _ => @workOf n)
  let G := fun z : unitInterval × PopulationSeed R => 144*L z + s^2*V z.1*W z
  have en : ∀ᵐ u ∂ν, u.2=(fun _=>g) := by
    dsimp [ν,populationSeedLaw]
    rw [Measure.infinitePi_dirac,Measure.prod_dirac]
    apply ae_map_iff (show Measurable (fun u : R => (u,fun _ : ℕ => g)) from
      measurable_id.prodMk measurable_const).aemeasurable (measurableSet_eq_fun measurable_snd measurable_const) |>.mpr
    exact ae_of_all _ fun _ => rfl
  have lm : Measurable L := measurable_priorExpect pol (measurable_populationPolicy A) populationGap measurable_populationGap _
    (fun w => (((hX w).comp measurable_snd).sub (measurable_subtype_coe.comp measurable_fst)).pow_const 2)
  have wm : Measurable W := measurable_priorExpect pol (measurable_populationPolicy A) populationGap measurable_populationGap _
    (fun _ => measurable_const)
  have gm : Measurable G := (measurable_const.mul lm).add ((measurable_const.mul (vm.comp measurable_fst)).mul wm)
  have lb (z) : |L z| ≤ 1 := by
    apply priorExpect_bound pol populationGap (fun u i => ⟨(u.2 i).property.1.le,(u.2 i).property.2⟩)
    intro p u w
    rw [abs_of_nonneg (sq_nonneg _)]
    have hx := hXb u w
    nlinarith [mul_nonneg (show 0 ≤ 1-X u w+p.val by linarith [hx.2,p.property.1])
      (show 0 ≤ 1+X u w-p.val by linarith [hx.1,p.property.2])]
  have wb (z) : |W z| ≤ n := priorExpect_bound pol populationGap
    (fun u i => ⟨(u.2 i).property.1.le,(u.2 i).property.2⟩) _ n
    (fun _ _ w => by rw [abs_of_nonneg (workOf_nonneg _)]; exact workOf_le_length _) z
  have li : Integrable L (volume.prod ν) := (integrable_const (1:ℝ)).mono' lm.aestronglyMeasurable (ae_of_all _ lb)
  have gi : Integrable G (volume.prod ν) := by
    apply (integrable_const (144+s^2*C*n)).mono' gm.aestronglyMeasurable
    apply ae_of_all
    intro z
    apply (abs_add_le ..).trans
    simp only [abs_mul,abs_of_nonneg (vb z.1).1,abs_of_nonneg (sq_nonneg s),abs_of_pos (by norm_num : (0:ℝ)<144)]
    apply add_le_add (by linarith [lb z]) (mul_le_mul_of_nonneg _ (wb z) (mul_nonneg (sq_nonneg s) (vb z.1).1) (by positivity))
    exact mul_le_mul_of_nonneg_left (vb z.1).2 (sq_nonneg s)
  have low : 20/3 ≤ ∫ p : unitInterval, ∫ u, G (p,u) ∂ν := by
    rw [integral_integral_swap (f := fun p u => G (p,u)) gi]
    have hh : ∀ᵐ u ∂ν, (20/3:ℝ) ≤ ∫ p : unitInterval, G (p,u) := by
      filter_upwards [en] with u hu
      have lI : Integrable (fun p => L (p,u)) volume := (integrable_const (1:ℝ)).mono'
        (lm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable (ae_of_all _ fun _ => lb _)
      have vwi : Integrable (fun p => s^2*V p*W (p,u)) volume := by
        apply (integrable_const (s^2*C*n)).mono'
          (((measurable_const.mul vm).mul (wm.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable)
        apply ae_of_all
        intro p
        change |s^2*V p*W (p,u)| ≤ _
        rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg s),abs_of_nonneg (vb p).1]
        exact mul_le_mul_of_nonneg (mul_le_mul_of_nonneg_left (vb p).2 (sq_nonneg _))
          (wb _) (mul_nonneg (sq_nonneg s) (vb p).1) (by positivity)
      change 20/3 ≤ ∫ p : unitInterval, 144*L (p,u)+s^2*V p*W (p,u)
      rw [integral_add (lI.const_mul 144) vwi,integral_const_mul]
      have hu' : populationGap u = fun _ => s/2 := by
        funext i
        unfold populationGap
        rw [hu]
        dsimp [s]
        ring
      simp only [L,W,priorExpect,hu',V]
      exact finite_critical_tradeoff (pol u) s hs hg (X u) K hK hprice
    have ih := integral_mono_ae (integrable_const (20/3:ℝ)) gi.integral_prod_right hh
    simpa using ih
  have up (p : unitInterval) : (∫ u, G (p,u) ∂ν) ≤ 144*(∫ u, L (p,u) ∂ν) + s^2*B*V p := by
    have lI : Integrable (fun u => L (p,u)) ν := (integrable_const (1:ℝ)).mono'
      (lm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (ae_of_all _ fun _ => lb _)
    have wI : Integrable (fun u => W (p,u)) ν := (integrable_const (n:ℝ)).mono'
      (wm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (ae_of_all _ fun _ => wb _)
    change (∫ u, 144*L (p,u)+(s^2*V p)*W (p,u) ∂ν) ≤ _
    rw [integral_add (lI.const_mul _) (wI.const_mul _),integral_const_mul,integral_const_mul]
    have hw : (∫ u, W (p,u) ∂ν) ≤ B := population_prefix_work_budget _ A B hB hb n p
    linarith only [mul_le_mul_of_nonneg_left hw (mul_nonneg (sq_nonneg s) (vb p).1)]
  have hh := integral_mono gi.integral_prod_left ((li.integral_prod_left.const_mul 144).add (vi.const_mul (s^2*B))) up
  change _ ≤ ∫ p : unitInterval, 144*(∫ u, L (p,u) ∂ν)+(s^2*B)*V p at hh
  rw [integral_add (li.integral_prod_left.const_mul 144) (vi.const_mul _),integral_const_mul,integral_const_mul,
    show s^2*B=4 from hbudget] at hh
  change (20/3-2*a)/144 ≤ ∫ p : unitInterval, ∫ u, L (p,u) ∂ν
  linarith only [low,hh,vavg]

/-- The square root of (20/3-2a)/144 exceeds one sixth when a is below 4/3. -/
theorem tapered_coefficient_gt (a : ℝ) (ha : a < 4/3) :
    (1/6:ℝ) < Real.sqrt ((20/3-2*a)/144) := by
  rw [Real.lt_sqrt (by norm_num)]
  linarith

/-! ### Upper histograms with an area cap below 2/3 -/

private def box (N : ℕ) (i : Fin N) : Set ℝ := Icc ((i.val:ℝ)/N) (((i.val:ℝ)+1)/N)

private def histogram {N : ℕ} (h : Fin N → ℝ) (t : ℝ) : ℝ :=
  ∑ i, (box N i).indicator (fun _ => h i) t

private theorem box_integral {N : ℕ} (n : 0<N) (i : Fin N) (H : ℝ) :
    (∫ t in (0:ℝ)..1, (box N i).indicator (fun _=>H) t) = H/(N:ℝ) := by
  have np : (0:ℝ)<N := by exact_mod_cast n
  have hi : (i.val:ℝ)+1 ≤ N := by exact_mod_cast i.isLt
  have sub : box N i ⊆ Icc (0:ℝ) 1 := by
    intro t ht
    exact ⟨(by positivity : (0:ℝ) ≤ (i.val:ℝ)/N).trans ht.1,ht.2.trans ((div_le_one np).mpr hi)⟩
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc,
    MeasureTheory.integral_indicator (show MeasurableSet (box N i) from measurableSet_Icc),
    Measure.restrict_restrict (show MeasurableSet (box N i) from measurableSet_Icc),
    inter_eq_left.mpr sub,integral_const]
  simp only [box,measureReal_def,Measure.restrict_apply_univ,Real.volume_Icc,smul_eq_mul]
  rw [show ((i.val:ℝ)+1)/N-i.val/N=1/(N:ℝ) by ring, ENNReal.toReal_ofReal (by positivity)]
  ring

/-- The rectangle transfer with the rescaled area cap a in place of 2/3. -/
theorem minimax_from_rectangles_slack (g : Gap) (B h : ℝ) (hs : 2*g.val ≤ h) (hh : h < 1)
    (hb : (2*g.val)^2*B=4) (N : ℕ) (hn : 0<N) (V : Fin N → ℝ)
    (nonneg : ∀ i, 0 ≤ V i) (a : ℝ) (ha : a ≤ 5/3)
    (sum : (h/(2*g.val))^2*((∑ i, V i)/(N:ℝ)) ≤ a)
    (price : ∀ i : Fin N, ∀ t ∈ Icc ((i.val:ℝ)/N) (((i.val:ℝ)+1)/N), t < 1 →
      ∃ P, 0 < P ∧ P ≤ 1 ∧ admissibleExitPrice h t P ∧ (1-t^2)^2 ≤ V i*P) :
    ENNReal.ofReal (Real.sqrt ((20/3-2*(2*a))/144)) ≤ minimaxRisk (Measure.dirac g) B := by
  let s := 2*g.val
  have sp : 0<s := by dsimp [s]; linarith [g.property.1]
  have hp := sp.trans_le hs
  have np : (0:ℝ)<N := by exact_mod_cast hn
  let C := (h/s)^2
  let E := histogram V
  let K := fun t : ℝ => C*E |t|
  have cm : ∀ i : Fin N, Measurable ((box N i).indicator (fun _=>V i)) :=
    fun i => measurable_const.indicator measurableSet_Icc
  have em : Measurable E := Finset.measurable_sum _ (fun i _ => cm i)
  have each (i : Fin N) (t : ℝ) : (box N i).indicator (fun _=>V i) t ∈ Icc 0 (V i) := by
    by_cases ht : t ∈ box N i <;> simp [ht,nonneg i]
  have ecap (t : ℝ) : E t ∈ Icc 0 (∑ i, V i) :=
    ⟨Finset.sum_nonneg (fun i _ => (each i t).1),Finset.sum_le_sum (fun i _ => (each i t).2)⟩
  have Ib (i : Fin N) : IntervalIntegrable ((box N i).indicator (fun _=>V i)) volume 0 1 := by
    apply IntervalIntegrable.mono_fun (intervalIntegrable_const (b := (1:ℝ)) (c := V i))
      (cm i).aestronglyMeasurable
    apply ae_of_all
    intro t
    simpa only [Real.norm_eq_abs,abs_of_nonneg (each i t).1,abs_of_nonneg (nonneg i)] using (each i t).2
  have ei : IntervalIntegrable E volume 0 1 := by
    have eqn : E = ∑ i : Fin N, (box N i).indicator (fun _ => V i) := by
      funext t
      simp [E,histogram,Finset.sum_apply]
    rw [eqn]
    exact IntervalIntegrable.sum Finset.univ (fun i _ => Ib i)
  have eint : (∫ t in (0:ℝ)..1, E t) = (∑ i, V i)/(N:ℝ) := by
    change (∫ t in (0:ℝ)..1, ∑ i, (box N i).indicator (fun _ => V i) t) = _
    rw [intervalIntegral.integral_finsetSum (fun i _ => Ib i),Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => box_integral hn i _)
  have eci := ei.const_mul C
  have contact : EqOn (fun t => C*E (-t)) K (uIoo (-1:ℝ) 0) := by
    rw [uIoo_of_le (by norm_num)]
    intro t ht
    simp [K,abs_of_neg ht.2]
  have contact' : EqOn (fun t => C*E t) K (uIoo (0:ℝ) 1) := by
    rw [uIoo_of_le zero_le_one]
    intro t ht
    simp [K,abs_of_pos ht.1]
  have reflected : IntervalIntegrable (fun t => C*E (-t)) volume (-1) 0 := by
    simpa only [neg_zero] using (IntervalIntegrable.iff_comp_neg (f := fun t => C*E t)
      (a := 1) (b := 0)).mp eci.symm
  have left := reflected.congr_uIoo contact
  have right := eci.congr_uIoo contact'
  apply minimax_from_tapered_price_slack g B (hs.trans_lt hh) hb K
    (measurable_const.mul (em.comp measurable_abs)) (left.trans right)
  · exact ⟨C*∑ i, V i,fun t _ => ⟨mul_nonneg (sq_nonneg _) (ecap _).1,
      mul_le_mul_of_nonneg_left (ecap _).2 (sq_nonneg _)⟩⟩
  · linarith only [ha]
  · rw [←intervalIntegral.integral_add_adjacent_intervals left right,
      ←intervalIntegral.integral_congr_uIoo contact,←intervalIntegral.integral_congr_uIoo contact',
      intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_neg]
    simp only [neg_zero,neg_neg,intervalIntegral.integral_const_mul,eint]
    change C*((∑ i, V i)/(N:ℝ)) + C*((∑ i, V i)/(N:ℝ)) ≤ _
    change C*((∑ i, V i)/(N:ℝ)) ≤ a at sum
    linarith only [sum]
  · intro t ht
    let j := ⌊abs t * N⌋₊
    have hj : j<N := (Nat.floor_lt (by positivity : 0 ≤ abs t * N)).mpr (by nlinarith only [mul_lt_mul_of_pos_right ht np])
    let i : Fin N := ⟨j,hj⟩
    have mem : |t| ∈ box N i :=
      ⟨(div_le_iff₀ np).mpr (Nat.floor_le (by positivity)),
        (le_div_iff₀ np).mpr (Nat.lt_floor_add_one _).le⟩
    obtain ⟨P,pp,p1,pa,pk⟩ := price i |t| mem ht
    have vi : V i ≤ E |t| := by
      have hi := Finset.single_le_sum (fun j _ => (each j |t|).1) (Finset.mem_univ i)
      simpa only [E,histogram,Set.indicator_of_mem mem] using hi
    have rpos : 0<(s/h)^2 := sq_pos_of_pos (div_pos sp hp)
    have rle : (s/h)^2≤1 := by
      have a := (div_le_one hp).mpr hs
      nlinarith [mul_nonneg (sub_nonneg.mpr a) (show 0≤1+s/h by positivity)]
    refine ⟨(s/h)^2*P,mul_pos rpos pp,(mul_le_mul_of_nonneg rle p1 rpos.le zero_le_one).trans_eq (by norm_num),
      interpolate_exit_price s h |t| P sp hs hh (abs_nonneg _) ht pp.le pa,?_⟩
    have q : K t*((s/h)^2*P)=E |t| * P := by dsimp [K,C]; field_simp
    rw [q,← sq_abs t]
    exact pk.trans (mul_le_mul_of_nonneg_right vi pp.le)

/-! ### A strict cover of the certified window -/

private def lastEndpoint (lo : ℕ) : List ℕ → ℕ
  | [] => lo
  | hi :: rest => lastEndpoint hi rest

private theorem chain_le_last (lo : ℕ) (rest : List ℕ) (ok : gridChain lo rest) :
    lo ≤ lastEndpoint lo rest := by
  induction rest generalizing lo with
  | nil => exact le_rfl
  | cons hi rest ih =>
    obtain ⟨bound, tail⟩ := ok
    exact bound.2.1.trans (ih hi tail)

/-- A point strictly above the start of a certified chain lies in a certified
interval whose left endpoint is strictly below it. -/
private theorem strict_cover (lo : ℕ) (rest : List ℕ) (nonempty : rest ≠ [])
    (ok : gridChain lo rest) (x : ℝ) (left : (lo:ℝ) < x)
    (right : x ≤ (lastEndpoint lo rest:ℝ)) :
    ∃ a b : ℕ, b ≤ lastEndpoint lo rest ∧ gridBound a b ∧ (a:ℝ) < x ∧ x ≤ (b:ℝ) := by
  induction rest generalizing lo with
  | nil => contradiction
  | cons hi rest ih =>
    obtain ⟨bound, tail⟩ := ok
    by_cases h : x ≤ (hi:ℝ)
    · exact ⟨lo,hi,chain_le_last hi rest tail,bound,left,h⟩
    · have hr : rest ≠ [] := by
        rintro rfl
        exact h right
      exact ih hi hr tail (lt_of_not_ge h) right

private theorem last_endpoint_value : lastEndpoint 16384 endpoints = 39936 := rfl

/-- Every bias strictly above 2/5 and at most 39/40 lies below a certified
grid endpoint whose rescaled upper sum is strictly below 2/3. -/
theorem strict_window_endpoint (s : ℝ) (hs : 2/5 < s) (hs' : s ≤ 39/40) :
    ∃ hi : ℕ, hi < biasDenominator ∧ s ≤ (hi:ℝ)/40960 ∧
      (((hi:ℝ)/40960)/s)^2 * ((upperSum hi:ℝ)/((bins:ℝ)*(scale:ℝ))) < 2/3 := by
  have hl : ((16384:ℕ):ℝ) < 40960*s := by push_cast; linarith
  have hr : 40960*s ≤ (lastEndpoint 16384 endpoints:ℝ) := by
    rw [last_endpoint_value]
    push_cast
    linarith
  obtain ⟨a,b,hb,hgrid,hl',hr'⟩ := strict_cover 16384 endpoints (List.cons_ne_nil _ _) checked_window (40960*s) hl hr
  rw [last_endpoint_value] at hb
  refine ⟨b,by unfold biasDenominator; omega,by linarith,?_⟩
  have hnat := hgrid.2.2
  have hreal : 3*(b:ℝ)^2*(upperSum b:ℝ) ≤ 2*(a:ℝ)^2*(bins:ℝ)*(scale:ℝ) := by
    exact_mod_cast hnat
  have a0 : (0:ℝ) < a := by exact_mod_cast hgrid.1
  have ha : (a:ℝ)^2 < (40960*s)^2 := by
    nlinarith only [mul_pos (sub_pos.mpr hl') (show 0 < 40960*s+(a:ℝ) by linarith)]
  have hpos : 0 < s := by linarith
  have bpos : 0 < (bins:ℝ) := by norm_num [bins]
  have spos : 0 < (scale:ℝ) := by norm_num [scale]
  have hraw : 3*(b:ℝ)^2*(upperSum b:ℝ) < 2*(40960*s)^2*(bins:ℝ)*(scale:ℝ) :=
    hreal.trans_lt (mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left ha (by norm_num : (0:ℝ) < 2)) bpos) spos)
  field_simp
  nlinarith only [hraw]

/-- The certified middle range with a strict margin. -/
theorem middle_minimax_strict (g : Gap) (B : ℝ) (h0 : 2/5 < 2*g.val)
    (h1 : 2*g.val ≤ 39/40) (hb : (2*g.val)^2*B=4) :
    ∃ c : ℝ, 1/6 < c ∧ ENNReal.ofReal c ≤ minimaxRisk (Measure.dirac g) B := by
  let s := 2*g.val
  obtain ⟨u,uw,up,area⟩ := strict_window_endpoint s h0 h1
  let h := (u:ℝ)/biasDenominator
  let a := (h/s)^2*((upperSum u:ℝ)/((bins:ℝ)*(scale:ℝ)))
  have ha : a < 2/3 := area
  have ww : (0:ℝ)<biasDenominator := by norm_num [biasDenominator]
  have hp : 0<u := by
    by_contra! hz
    have : u=0 := by omega
    rw [this] at up
    simp only [Nat.cast_zero,zero_div] at up
    linarith only [h0,up]
  let V := fun i : Fin bins => (rectangleHeight (i.val+1) u biasDenominator:ℝ)/scale
  refine ⟨_,tapered_coefficient_gt (2*a) (by linarith only [ha]),?_⟩
  apply minimax_from_rectangles_slack g B h up ((div_lt_one ww).mpr (by exact_mod_cast uw)) hb
    bins (by norm_num [bins]) V (fun _ => by dsimp [V]; positivity) a (by linarith only [ha])
  · change (h/s)^2*((∑ i : Fin bins, (rectangleHeight (i.val+1) u biasDenominator:ℝ)/(scale:ℝ))/(bins:ℝ)) ≤ a
    rw [upperSum_real]
  · intro i t mem ht
    exact grid_price u biasDenominator hp uw i t mem ht

/-! ### Near-perfect coins with a strict integral -/

/-- The near-perfect envelope integrates to strictly less than 2/3 below s=1. -/
theorem near_perfect_integral_strict (s : ℝ) (hs : 39/40 ≤ s) (hs' : s < 1) :
    IntervalIntegrable (nearPerfectEnvelope s) volume 0 1 ∧
    (∫ t in (0:ℝ)..1, nearPerfectEnvelope s t) < 2/3 := by
  let a := (3/4:ℝ)
  let V := fun t : ℝ => 1-t^2
  let M := fun t : ℝ => (1-s^2)*(V t*t^2)
  let f := nearPerfectEnvelope s
  have hv : Continuous V := by dsimp [V]; fun_prop
  have hm : Continuous M := by dsimp [M]; fun_prop
  have left : Set.EqOn (fun t => V t-M t) f (Set.uIoo 0 a) := by
    rw [Set.uIoo_of_le (by dsimp [a]; norm_num)]
    intro t ht
    exact (ite_eq_left ht.2.le).symm
  have right : Set.EqOn (fun t => V t/s^2) f (Set.uIoo a 1) := by
    rw [Set.uIoo_of_le (by dsimp [a]; norm_num)]
    intro t ht
    exact (ite_eq_right (not_le_of_gt ht.1)).symm
  have hL : IntervalIntegrable f volume 0 a :=
    ((hv.sub hm).intervalIntegrable ..).congr_uIoo left
  have hR : IntervalIntegrable f volume a 1 :=
    ((hv.div_const _).intervalIntegrable ..).congr_uIoo right
  refine ⟨hL.trans hR,?_⟩
  change (∫ t in (0:ℝ)..1, f t) < _
  rw [← intervalIntegral.integral_add_adjacent_intervals hL hR,
    ← intervalIntegral.integral_congr_uIoo left,← intervalIntegral.integral_congr_uIoo right,
    intervalIntegral.integral_sub (hv.intervalIntegrable ..) (hm.intervalIntegrable ..),
    intervalIntegral.integral_div]
  have iV (l r : ℝ) : (∫ t in l..r, V t) = (r-l)-(r^3-l^3)/3 := by
    dsimp [V]
    rw [intervalIntegral.integral_sub (intervalIntegrable_const) (Continuous.intervalIntegrable (by fun_prop) ..),
      intervalIntegral.integral_const,integral_pow]
    norm_num
  have iM : (∫ t in (0:ℝ)..a, M t) = (1-s^2)*(477/5120) := by
    dsimp [M,V,a]
    rw [intervalIntegral.integral_const_mul]
    have eqn (t : ℝ) : (1-t^2)*t^2 = t^2-t^4 := by ring
    simp_rw [eqn]
    rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) ..)
      (Continuous.intervalIntegrable (by fun_prop) ..),integral_pow,integral_pow]
    norm_num
  rw [iV,iM,iV]
  dsimp [a]
  have hpos : 0 < s := by linarith
  have hs2 : (39/40:ℝ)^2 ≤ s^2 := by nlinarith [mul_nonneg (show 0 ≤ s-39/40 by linarith) (show 0 ≤ s+39/40 by linarith)]
  have hlt : 0 < 1-s^2 := by nlinarith [mul_pos (sub_pos.mpr hs') (show 0 < 1+s by linarith)]
  field_simp
  nlinarith only [mul_pos hlt (show 0 < (477/5120)*s^2-11/192 by linarith only [hs2])]

/-- Critical single-gap bound for near-perfect coins with a strict margin. -/
theorem near_perfect_minimax_strict (g : Gap) (B : ℝ) (hg : 39/40 ≤ 2*g.val)
    (h1 : 2*g.val < 1) (hbudget : (2*g.val)^2*B = 4) :
    ∃ c : ℝ, 1/6 < c ∧ ENNReal.ofReal c ≤ minimaxRisk (Measure.dirac g) B := by
  let s := 2*g.val
  let E := nearPerfectEnvelope s
  let K := fun t : ℝ => E |t|
  have hs : 0 < s := by dsimp [s]; linarith [g.property.1]
  have s2 : s^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr h1.le) (show 0 ≤ 1+s by linarith)]
  obtain ⟨hi,hh⟩ := near_perfect_integral_strict s hg h1
  have contact : Set.EqOn (fun t => E (-t)) K (Set.uIoo (-1:ℝ) 0) := by
    rw [Set.uIoo_of_le (by norm_num)]
    intro t ht
    simp [K,abs_of_neg ht.2]
  have contact' : Set.EqOn E K (Set.uIoo (0:ℝ) 1) := by
    rw [Set.uIoo_of_le zero_le_one]
    intro t ht
    simp [K,abs_of_pos ht.1]
  have reflected : IntervalIntegrable (fun t => E (-t)) volume (-1) 0 := by
    simpa only [neg_zero] using (IntervalIntegrable.iff_comp_neg (f := E) (a := 1) (b := 0)).mp hi.symm
  have left := reflected.congr_uIoo contact
  have right := hi.congr_uIoo contact'
  refine ⟨_,tapered_coefficient_gt (2*(∫ t in (0:ℝ)..1, E t)) (by linarith only [hh]),?_⟩
  apply minimax_from_tapered_price_slack g B h1 hbudget K
  · dsimp [K,E,nearPerfectEnvelope]
    apply Measurable.ite (measurableSet_le measurable_abs measurable_const) <;> fun_prop
  · exact left.trans right
  · refine ⟨1+1/s^2,?_⟩
    intro t ht
    let u := |t|
    have hu0 : 0 ≤ u := abs_nonneg t
    have hu1 : u ≤ 1 := abs_le.mpr ht
    have v : 0 ≤ 1-u^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (show 0 ≤ 1+u by linarith)]
    have inv : 0 ≤ 1/s^2 := by positivity
    change 0 ≤ nearPerfectEnvelope s u ∧ nearPerfectEnvelope s u ≤ _
    unfold nearPerfectEnvelope
    split_ifs
    · have h := mul_nonneg v (show 0 ≤ 1-(1-s^2)*u^2 by nlinarith [mul_nonneg (sq_nonneg s) (sq_nonneg u)])
      constructor
      · linarith only [h]
      · nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr s2) v) (sq_nonneg u),sq_nonneg u]
    · constructor
      · positivity
      · apply le_trans (div_le_div_of_nonneg_right (show 1-u^2 ≤ 1 by nlinarith [sq_nonneg u]) (sq_nonneg s))
        linarith
  · linarith only [hh]
  · rw [← intervalIntegral.integral_add_adjacent_intervals left right,
      ← intervalIntegral.integral_congr_uIoo contact,← intervalIntegral.integral_congr_uIoo contact',
      intervalIntegral.integral_comp_neg]
    simp only [neg_zero,neg_neg]
    linarith
  · intro t ht
    have h := near_perfect_envelope s |t| hg h1 (abs_nonneg _) ht
    exact ⟨nearPerfectReciprocal s |t|,h.1,h.2.1,near_perfect_admissible s |t| hg h1 (abs_nonneg _) ht,
      by simpa only [sq_abs] using h.2.2⟩

/-! ### Assembly -/

/-- Every critical point mass with flip bias below one has a coefficient
strictly above one sixth. -/
theorem critical_minimax_strict (g : Gap) (B : ℝ) (hg : 2*g.val < 1) (hb : (2*g.val)^2*B=4) :
    ∃ c : ℝ, 1/6 < c ∧ ENNReal.ofReal c ≤ minimaxRisk (Measure.dirac g) B := by
  by_cases weak : 2*g.val ≤ 2/5
  · refine ⟨Real.sqrt (59/2100),?_,weak_gap_minimax_lower g B weak hb⟩
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  by_cases mid : 2*g.val ≤ 39/40
  · exact middle_minimax_strict g B (lt_of_not_ge weak) mid hb
  · exact near_perfect_minimax_strict g B (lt_of_not_ge mid).le hg hb

private theorem critical_above_four (B : ℝ) (hb : 4 < B) :
    ∃ g : Gap, g.val=1/Real.sqrt B ∧ 2*g.val < 1 ∧ (2*g.val)^2*B=4 := by
  have hr : (2:ℝ) < Real.sqrt B := (Real.lt_sqrt (by norm_num)).2 (by linarith)
  have hp : 0 < Real.sqrt B := by linarith
  let g : Gap := ⟨1/Real.sqrt B,one_div_pos.mpr hp,(div_le_iff₀ hp).2 (by linarith)⟩
  refine ⟨g,rfl,?_,?_⟩
  · change 2*(1/Real.sqrt B) < 1
    rw [mul_one_div,div_lt_one hp]
    exact hr
  · change (2*(1/Real.sqrt B))^2*B=4
    field_simp [hp.ne']
    nlinarith only [Real.sq_sqrt (show 0 ≤ B by linarith)]

/-- One coefficient strictly above one sixth works for every gap law at each
budget at least one other than four. -/
theorem uniform_strict_coefficient (B : ℝ) (hB : 1 ≤ B) (h4 : B ≠ 4) : ∃ c : ℝ, 1/6 < c ∧
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤ minimaxRisk μ B := by
  rcases lt_or_gt_of_ne h4 with small | large
  · refine ⟨Real.sqrt ((10-B)/216),?_,fun μ _ => ?_⟩
    · rw [Real.lt_sqrt (by norm_num)]
      linarith
    · apply le_trans _ (small_budget_minimax_lower μ B (by linarith) (by linarith))
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_of_le_one_left (Real.sqrt_nonneg _)
        (modulus_le_one μ (show 0 ≤ 1/Real.sqrt B by positivity))
  · obtain ⟨g,hg,hs,crit⟩ := critical_above_four B large
    obtain ⟨c,hc,low⟩ := critical_minimax_strict g B hs crit
    refine ⟨c,hc,fun μ _ => ?_⟩
    rw [←hg,ENNReal.ofReal_mul (modulus_pos μ g.property.1).le]
    exact (mul_le_mul_right low _).trans (critical_gap_reduction μ g B)

private theorem sixth_lt (μ : Measure Gap) [IsProbabilityMeasure μ] (B c : ℝ) (hB : 1 ≤ B)
    (hc : 1/6 < c) :
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) <
      ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) := by
  have hω := modulus_pos μ (show 0 < 1/Real.sqrt B by positivity)
  apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos hω (by linarith))).mpr
  nlinarith only [hω,hc]

/-- Strictness for every gap law and every budget at least one other than four. -/
theorem minimax_strict_lower (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) (hB : 1 ≤ B)
    (h4 : B ≠ 4) : ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) < minimaxRisk μ B := by
  obtain ⟨c,hc,low⟩ := uniform_strict_coefficient B hB h4
  exact (sixth_lt μ B c hB hc).trans_le (low μ)

theorem equality_forces_four (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) (hB : 1 ≤ B)
    (heq : minimaxRisk μ B = ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6)) : B = 4 := by
  by_contra h4
  exact (minimax_strict_lower μ B hB h4).ne heq.symm

theorem small_budget_minimax_lower_four (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ)
    (hB : 0 ≤ B) (h4 : B ≤ 4) : ENNReal.ofReal (Real.sqrt ((10 - B) / 216)) ≤ minimaxRisk μ B :=
  small_budget_minimax_lower μ B hB (by linarith)

theorem critical_point_strict (g : Gap) (B : ℝ) (hg : 2 * g.val < 1) (hb : (2 * g.val) ^ 2 * B = 4) :
    ENNReal.ofReal (1/6 : ℝ) < minimaxRisk (Measure.dirac g) B := by
  obtain ⟨c,hc,low⟩ := critical_minimax_strict g B hg hb
  exact ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hc).trans_le low

/-! ### Both magnitude oracles -/

private def cappedGap (h : ℝ) (hp : 0 < h) : Gap := ⟨min (1/2) h,lt_min (by norm_num) hp,min_le_left ..⟩

private theorem capped_modulus (μ : Measure Gap) (h : ℝ) (hp : 0<h) :
    modulus μ (cappedGap h hp).val = modulus μ h := by
  unfold modulus
  apply integral_congr_ae
  apply ae_of_all
  intro d
  by_cases hh : h ≤ 1/2
  · simp only [cappedGap,min_eq_right hh]
  · have h0 : 1 ≤ (1/2)/d.val := (one_le_div d.property.1).2 d.property.2
    have h1 : 1 ≤ h/d.val := (one_le_div d.property.1).2 (d.property.2.trans (le_of_not_ge hh))
    simp only [cappedGap,clippedGap,min_eq_left (le_of_not_ge hh),min_eq_left h0,min_eq_left h1]

private theorem capped_dirac (h : ℝ) (hp : 0<h) :
    modulus (Measure.dirac (cappedGap h hp)) h=1 := by
  simp only [modulus,integral_dirac,clippedGap]
  exact min_eq_left ((one_le_div (cappedGap h hp).property.1).2 (min_le_right ..))

private theorem lift_lower (μ : Measure Gap) [IsProbabilityMeasure μ] (B h c : ℝ) (hp : 0<h)
    (low : ∀ g : Gap, ENNReal.ofReal (modulus (Measure.dirac g) h*c) ≤ minimaxRisk (Measure.dirac g) B) :
    ENNReal.ofReal (modulus μ h*c) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ h*c) ≤ selectedMinimaxRisk μ B := by
  let g := cappedGap h hp
  have crit : ENNReal.ofReal c ≤ minimaxRisk (Measure.dirac g) B := by
    simpa only [g,capped_dirac,one_mul] using low g
  have all (R : Type) [MeasurableSpace R] (A : OracleEstimator R) (hb : OracleBudget A B) :
      ENNReal.ofReal (modulus μ h*c) ≤ oracleRisk μ A := by
    rw [←capped_modulus μ h hp,ENNReal.ofReal_mul (modulus_pos μ g.property.1).le]
    exact (mul_le_mul_right crit _).trans (oracle_gap_reduction μ g A B hb)
  constructor
  · apply le_sInf
    rintro x ⟨R,mR,A,hb,rfl⟩
    exact all _ (revealedOracle μ A) hb
  · apply le_sInf
    rintro x ⟨R,mR,A,hb,rfl⟩
    exact all R (selectedOracle A) hb

/-- Strictness with every magnitude revealed and with selected magnitudes. -/
theorem oracle_minimax_strict (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) (hB : 1 ≤ B)
    (h4 : B ≠ 4) :
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) < revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) < selectedMinimaxRisk μ B := by
  obtain ⟨c,hc,low⟩ := uniform_strict_coefficient B hB h4
  have lift := lift_lower μ B (1/Real.sqrt B) c (by positivity) (fun g => low (Measure.dirac g))
  exact ⟨(sixth_lt μ B c hB hc).trans_le lift.1,(sixth_lt μ B c hB hc).trans_le lift.2⟩

end ThresholdHC.SharpStrict
