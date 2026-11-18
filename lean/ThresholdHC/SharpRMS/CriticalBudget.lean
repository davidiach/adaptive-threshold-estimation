import ThresholdHC.SharpRMS.AdaptivePrice
import ThresholdHC.SharpRMS.Score
import ThresholdHC.SharpRMS.PriceBounds
import ThresholdHC.SharpRMS.FourBudget

/-! Passing an integrable tapered price bound to the critical single-gap
experiment with arbitrary private randomization and unbounded stopping. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory Set Filter Tier3 Tier5 Tier6
open scoped ENNReal Topology unitInterval

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

/-- Sufficient scalar price condition for the actual unrestricted
single-gap population minimax risk. It includes the averaging over random
seeds, all horizons and arbitrary measurable output. -/
theorem minimax_from_tapered_price (g : Gap) (B : ℝ) (hg : 2*g.val < 1)
    (hbudget : (2*g.val)^2*B=4) (K : ℝ → ℝ) (hm : Measurable K)
    (hK : IntervalIntegrable K volume (-1) 1)
    (hcap : ∃ C : ℝ, ∀ t ∈ Icc (-1:ℝ) 1, 0 ≤ K t ∧ K t ≤ C)
    (havg : (∫ t in (-1:ℝ)..1, K t) ≤ 4/3)
    (hprice : ∀ t, |t| < 1 → ∃ P, 0 < P ∧ P ≤ 1 ∧ admissibleExitPrice (2*g.val) |t| P ∧
      (1-t^2)^2 ≤ K t*P) : ENNReal.ofReal (1/6:ℝ) ≤ minimaxRisk (Measure.dirac g) B := by
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
  have vavg : (∫ p : unitInterval, V p) ≤ 2/3 := by linarith only [uniform_transform K,havg]
  apply minimax_from_prefix_bayes
  intro R _ A hb n X hX hXb
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
  change 1/36 ≤ ∫ p : unitInterval, ∫ u, L (p,u) ∂ν
  linarith only [low,hh,vavg]

/-- Critical single-gap lower bound for near-perfect coins. -/
theorem near_perfect_minimax_lower (g : Gap) (B : ℝ) (hg : 39/40 ≤ 2*g.val)
    (h1 : 2*g.val < 1) (hbudget : (2*g.val)^2*B = 4) :
    ENNReal.ofReal (1/6:ℝ) ≤ minimaxRisk (Measure.dirac g) B := by
  let s := 2*g.val
  let E := nearPerfectEnvelope s
  let K := fun t : ℝ => E |t|
  have hs : 0 < s := by dsimp [s]; linarith [g.property.1]
  have s2 : s^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr h1.le) (show 0 ≤ 1+s by linarith)]
  obtain ⟨hi,hh⟩ := near_perfect_integral s hg h1
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
  apply minimax_from_tapered_price g B h1 hbudget K
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
  · rw [← intervalIntegral.integral_add_adjacent_intervals left right,
      ← intervalIntegral.integral_congr_uIoo contact,← intervalIntegral.integral_congr_uIoo contact',
      intervalIntegral.integral_comp_neg]
    simp only [neg_zero,neg_neg]
    linarith
  · intro t ht
    have h := near_perfect_envelope s |t| hg h1 (abs_nonneg _) ht
    exact ⟨nearPerfectReciprocal s |t|,h.1,h.2.1,near_perfect_admissible s |t| hg h1 (abs_nonneg _) ht,
      by simpa only [sq_abs] using h.2.2⟩

end ThresholdHC.SharpRMS
