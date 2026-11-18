import ThresholdHC.LargeBudgetRMS.LargeBudgetRisk
import ThresholdHC.SharpRMS.WeakPopulation

/-! The three-bias test for randomized estimators under uniform expected work. -/
noncomputable section
namespace ThresholdHC.SharpRMS.LargeBudget
open MeasureTheory Filter Real Tier3 Tier4 Tier5 Tier6
open scoped ENNReal Topology

private def constantLaw (t : ℝ) (ht : |t| ≤ 1) : SignLaw :=
  ⟨fun _ => (1+t)/2, measurable_const, fun _ =>
    ⟨by linarith [(abs_le.mp ht).1], by linarith [(abs_le.mp ht).2]⟩⟩

private theorem seed_measurable {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (s t : ℝ) {n : ℕ} (f : R → Prefix n → ℝ) (hf : ∀ w, Measurable (fun u => f u w)) :
    Measurable (fun u => prefixExpect (A.policy u) s t (f u)) := by
  apply Finset.measurable_sum
  intro w _
  exact (measurable_creationLaw A.policy A.policy_measurable _ _ (fun _ => measurable_const)
    (fun _ => measurable_const) w).mul (hf w)

private theorem seed_integrable {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : |t| ≤ 1) {n : ℕ}
    (f : R → Prefix n → ℝ) (hf : ∀ w, Measurable (fun u => f u w))
    (C : ℝ) (hC : ∀ u w, |f u w| ≤ C) :
    Integrable (fun u => prefixExpect (A.policy u) s t (f u)) A.randomLaw := by
  apply (integrable_const C).mono' (seed_measurable A s t f hf).aestronglyMeasurable
  apply ae_of_all
  intro u
  let p := creationLaw (n := n) (A.policy u) (fun _=>s/2) (fun _=>(1+t)/2)
  have hp := creationLaw_total n (A.policy u) (fun _=>s/2) (fun _=>(1+t)/2)
    (fun _=>⟨by linarith, by linarith⟩) (fun _=>⟨by linarith [(abs_le.mp ht).1],by linarith [(abs_le.mp ht).2]⟩)
  change |∑ w, p w*f u w| ≤ C
  calc
    _ ≤ ∑ w, |p w*f u w| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ w, p w*C := by
      apply Finset.sum_le_sum
      intro w _
      rw [abs_mul, abs_of_nonneg (hp.1 w)]
      exact mul_le_mul_of_nonneg_left (hC u w) (hp.1 w)
    _ = C := by rw [← Finset.sum_mul,show ∑ w, p w = 1 from hp.2,one_mul]

private theorem dirac_prefix {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (g : Gap) (t : ℝ) (ht : |t| ≤ 1) {n : ℕ} (f : R → Prefix n → ℝ)
    (hf : ∀ w, Measurable (fun u => f u w)) (hbound : ∃ C, ∀ u w, |f u w| ≤ C) :
    (∫ z, f z.1.1 (processPrefix n z.2) ∂experimentLaw (Measure.dirac g) A (constantLaw t ht)) =
    ∫ u, prefixExpect (A.policy u) (2*g.val) t (f u) ∂A.randomLaw := by
  obtain ⟨C,hC⟩ := hbound
  let q := constantLaw t ht
  let F := fun (u : PopulationSeed R) (w : Prefix n) => f u.1 w
  have hr := (population_realization R (Measure.dirac g) A q).2 n F
    (fun w => (hf w).comp measurable_fst) ⟨C,fun u w => hC u.1 w⟩
  have hm : Measurable (fun u : PopulationSeed R => ∑ w,
      creationLaw (populationPolicy A u) (populationGap u) (populationPrior q u) w * F u w) := by
    apply Finset.measurable_sum
    intro w _
    exact (measurable_creationLaw _ (measurable_populationPolicy A) _ _
      measurable_populationGap (measurable_populationPrior q) w).mul ((hf w).comp measurable_fst)
  have hmap : Measurable (fun u : R => (u, fun _ : ℕ => g)) := measurable_id.prodMk measurable_const
  rw [populationSeedLaw,Measure.infinitePi_dirac,Measure.prod_dirac,
    integral_map hmap.aemeasurable hm.aestronglyMeasurable] at hr
  unfold prefixExpect
  rw [show 2*g.val/2 = g.val by ring]
  exact hr

private theorem population_risk_work {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (g : Gap) (hg : 2*g.val < 1) (B : ℝ) (hB : 0 ≤ B) (hb : UniformBudget (Measure.dirac g) A B)
    (X : R × ProcessTape → ℝ) (hm : Measurable X) (hx : ∀ z, |X z| ≤ 1) :
    let risk := fun (t : ℝ) (ht : |t| ≤ 1) =>
      ∫ z, (X (z.1.1,z.2)-t)^2 ∂experimentLaw (Measure.dirac g) A (constantLaw t ht)
    (floorLog+2*(1-intercept)) ≤ tilt*risk 0 (by norm_num) + weight*risk bias (by norm_num) +
      weight*risk (-bias) (by norm_num) + charge (2*g.val) bias*B := by
  let s := 2*g.val
  have hs : 0 < s := by dsimp [s]; linarith [g.property.1]
  let D := fun (t : ℝ) (ht : |t| ≤ 1) => experimentLaw (Measure.dirac g) A (constantLaw t ht)
  let loss := fun (t : ℝ) (z : PopulationSeed R × ProcessTape) => (X (z.1.1,z.2)-t)^2
  let LS := fun (n : ℕ) (t : ℝ) (u : R) (w : Prefix n) => (X (u,padPrefix n w)-t)^2
  let G := fun n t u => prefixExpect (A.policy u) s t (LS n t u)
  let W := fun (n : ℕ) u => prefixExpect (A.policy u) s 0 (@workOf n)
  let price := charge s bias
  have hprice : 0 ≤ price := by
    apply neg_nonneg.mpr
    apply log_nonpos
    · have sq : s^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hg.le) (show 0≤1+s by linarith)]
      nlinarith only [sq,show bias^2≤1 by norm_num,sq_nonneg s,mul_nonneg (show 0≤1-bias^2 by norm_num) (sq_nonneg s)]
    · nlinarith only [mul_nonneg (sq_nonneg bias) (sq_nonneg s)]
  have hLm (t : ℝ) : Measurable (loss t) :=
    ((hm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).sub measurable_const).pow_const 2
  have bound (x t : ℝ) (h₁ : |x| ≤ 1) (h₂ : |t| ≤ 1) : |(x-t)^2| ≤ 4 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [mul_nonneg (show 0 ≤ 2-x+t by linarith [(abs_le.mp h₁).2,(abs_le.mp h₂).1])
      (show 0 ≤ 2+x-t by linarith [(abs_le.mp h₁).1,(abs_le.mp h₂).2])]
  have hLS (n) (t : ℝ) (w : Prefix n) : Measurable (fun u => LS n t u w) :=
    ((hm.comp (measurable_id.prodMk measurable_const)).sub measurable_const).pow_const 2
  have Gi n t (ht : |t| ≤ 1) : Integrable (G n t) A.randomLaw :=
    seed_integrable A s t hs.le hg.le ht _ (hLS n t) 4 (fun u w => bound _ _ (hx _) ht)
  have Wi n : Integrable (W n) A.randomLaw :=
    seed_integrable A s 0 hs.le hg.le (by norm_num) _ (fun _ => measurable_const) n
      (fun u w => by rw [abs_of_nonneg (workOf_nonneg _)]; exact workOf_le_length _)
  have Wle n : (∫ u, W n u ∂A.randomLaw) ≤ B := by
    have he := dirac_prefix A g 0 (by norm_num) (fun _ => @workOf n) (fun _ => measurable_const)
      ⟨(n:ℝ),fun u w => by rw [abs_of_nonneg (workOf_nonneg _)]; exact workOf_le_length _⟩
    exact he.ge.trans (prefix_work_le A _ _ B hB hb n)
  have lim t (ht : |t| ≤ 1) : Tendsto (fun n => ∫ u, G n t u ∂A.randomLaw) atTop
      (𝓝 (∫ z, loss t z ∂D t ht)) := by
    have h := limit_prefix A (Measure.dirac g) (constantLaw t ht) B hb (loss t) (hLm t) 4
      (fun z => bound _ _ (hx _) ht)
    apply h.congr
    intro n
    exact dirac_prefix A g t ht (LS n t) (hLS n t) ⟨4, fun u w => bound _ _ (hx _) ht⟩
  have hbnd (n : ℕ) : (floorLog+2*(1-intercept)) ≤ tilt*(∫ u, G n 0 u ∂A.randomLaw) +
      weight*(∫ u, G n bias u ∂A.randomLaw) + weight*(∫ u, G n (-bias) u ∂A.randomLaw) + price*B := by
    let H := fun u => tilt*G n 0 u + weight*G n bias u + weight*G n (-bias) u + price*W n u
    have h0 := (Gi n 0 (by norm_num)).const_mul tilt
    have hp := (Gi n bias (by norm_num)).const_mul weight
    have hn := (Gi n (-bias) (by norm_num)).const_mul weight
    have hw := (Wi n).const_mul price
    have locally (u : R) : floorLog+2*(1-intercept) ≤ H u := by
      have hh := prefix_test (A.policy u) s hs hg (fun w : Prefix n => X (u,padPrefix n w)) (fun _ => hx _)
      simpa only [H,G,LS,W,sub_zero,sub_neg_eq_add,price] using hh
    have hpoint := integral_mono (μ := A.randomLaw) (integrable_const (floorLog+2*(1-intercept)))
      (((h0.add hp).add hn).add hw) locally
    have h₁ := integral_add ((h0.add hp).add hn) hw
    have h₂ := integral_add (h0.add hp) hn
    simp only [Pi.add_apply] at hpoint h₁ h₂
    rw [h₁,h₂,integral_add h0 hp] at hpoint
    simp only [integral_const,probReal_univ,one_smul,integral_const_mul] at hpoint
    linarith only [hpoint,mul_le_mul_of_nonneg_left (Wle n) hprice]
  exact ge_of_tendsto ((((tendsto_const_nhds.mul (lim 0 (by norm_num))).add
    (tendsto_const_nhds.mul (lim bias (by norm_num)))).add
    (tendsto_const_nhds.mul (lim (-bias) (by norm_num)))).add tendsto_const_nhds)
    (Eventually.of_forall hbnd)


/-- A critical point-mass experiment gives a lower bound at any radius whose
three-bias test pays for the fair-law work at the given budget. -/
theorem critical_of_price (g : Gap) (B r : ℝ) (hr : 0<r) (hg : 2*g.val<1)
    (hbudget : (2*g.val)^2*B=4)
    (price : 4*(tilt+2*weight)*r^2 + charge (2*g.val) bias*B ≤ floorLog+2*(1-intercept)) :
    ENNReal.ofReal r ≤ minimaxRisk (Measure.dirac g) B := by
  let s := 2*g.val
  have hs : 0 < s := by dsimp [s]; linarith [g.property.1]
  have hB : 0 ≤ B := by
    by_contra! hh
    have hneg := mul_neg_of_pos_of_neg (sq_pos_of_pos hs) hh
    linarith
  apply le_sInf
  rintro _ ⟨R,mR,A,hb,rfl⟩
  by_contra! hsmall
  let μ := Measure.dirac g
  let X := fun z : R × ProcessTape => max (-1:ℝ) (min 1 (2*A.output z-1))
  have hm : Measurable X := by
    dsimp [X]
    exact measurable_const.max (measurable_const.min ((measurable_const.mul A.output_measurable).sub measurable_const))
  have hx (z) : |X z| ≤ 1 := abs_le.mpr ⟨le_max_left .., max_le (by norm_num) (min_le_left ..)⟩
  let risk := fun (t : ℝ) (ht : |t| ≤ 1) =>
    ∫ z, (X (z.1.1,z.2)-t)^2 ∂experimentLaw μ A (constantLaw t ht)
  have small (t : ℝ) (ht : |t| ≤ 1) : risk t ht < 4*r^2 := by
    let q := constantLaw t ht
    let P := experimentLaw μ A q
    let val := (1+t)/2
    have hav : signMean μ q.val = val := by simp [μ,q,constantLaw,signMean,val]
    have rms := (le_iSup (fun q' => rootMeanRisk (experimentLaw μ A q') (populationOutput A) (signMean μ q'.val)) q).trans_lt hsmall
    rw [hav] at rms
    have hsq : squaredRisk P (populationOutput A) val < ENNReal.ofReal (r^2) := by
      by_contra! hh
      have he := ENNReal.rpow_le_rpow hh (by norm_num : (0:ℝ) ≤ 1/2)
      rw [ofReal_square_rpow_half r hr.le] at he
      exact (not_le_of_gt rms) he
    have hi : Integrable (fun z : PopulationSeed R × ProcessTape => (X (z.1.1,z.2)-t)^2) P := by
      have hmeas : Measurable (fun z : PopulationSeed R × ProcessTape => (X (z.1.1,z.2)-t)^2) := ((hm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).sub
        (measurable_const (a := t))).pow_const 2
      apply (integrable_const (4:ℝ)).mono' hmeas.aestronglyMeasurable
      apply ae_of_all
      intro z
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hn := abs_le.mp (hx (z.1.1,z.2))
      nlinarith [mul_nonneg (show 0 ≤ 2-X (z.1.1,z.2)+t by linarith [(abs_le.mp ht).1,hn.2])
        (show 0 ≤ 2+X (z.1.1,z.2)-t by linarith [(abs_le.mp ht).2,hn.1])]
    have clip (z : PopulationSeed R × ProcessTape) :
        (X (z.1.1,z.2)-t)^2 ≤ 4*(populationOutput A z-val)^2 := by
      let x := 2*populationOutput A z-1
      have he : 4*(populationOutput A z-val)^2 = (x-t)^2 := by dsimp [x,val]; ring
      rw [he]
      change (max (-1:ℝ) (min 1 x)-t)^2 ≤ (x-t)^2
      obtain ⟨htl,htr⟩ := abs_le.mp ht
      rcases le_total x (-1) with hh | hh
      · rw [min_eq_right (by linarith),max_eq_left hh]
        nlinarith [mul_nonneg (show 0 ≤ -1-x by linarith) (show 0 ≤ 2*t+1-x by linarith)]
      · rcases le_total x 1 with hx' | hx'
        · rw [min_eq_right hx',max_eq_right hh]
        · rw [min_eq_left hx',max_eq_right (by norm_num)]
          nlinarith [mul_nonneg (show 0 ≤ x-1 by linarith) (show 0 ≤ x+1-2*t by linarith)]
    have hc : ENNReal.ofReal (risk t ht) ≤ ENNReal.ofReal 4 * squaredRisk P (populationOutput A) val := by
      unfold risk
      rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _), squaredRisk,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_mono fun z => (ENNReal.ofReal_le_ofReal (clip z)).trans_eq (ENNReal.ofReal_mul (by norm_num))
    have hh := hc.trans_lt (ENNReal.mul_lt_mul_right (by norm_num : ENNReal.ofReal (4:ℝ) ≠ 0) ENNReal.ofReal_ne_top hsq)
    rw [← ENNReal.ofReal_mul (by norm_num)] at hh
    by_contra! hn
    exact (not_le_of_gt hh) (ENNReal.ofReal_le_ofReal hn)
  have hmain := population_risk_work A g hg B hB hb X hm hx
  change floorLog+2*(1-intercept) ≤ tilt*risk 0 _ + weight*risk bias _ + weight*risk (-bias) _ + charge s bias*B at hmain
  have h0 := mul_lt_mul_of_pos_left (small 0 (by norm_num)) (show 0<tilt by norm_num)
  have hp := mul_lt_mul_of_pos_left (small bias (by norm_num)) (show 0<weight by norm_num)
  have hn := mul_lt_mul_of_pos_left (small (-bias) (by norm_num)) (show 0<weight by norm_num)
  change 4*(tilt+2*weight)*r^2 + charge s bias*B ≤ _ at price
  have bad : (0:ℝ)<0 := by linear_combination hmain + h0 + hp + hn + price
  exact (lt_irrefl _ bad)

end ThresholdHC.SharpRMS.LargeBudget
