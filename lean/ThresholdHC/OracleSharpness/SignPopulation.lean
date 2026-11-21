import ThresholdHC.OracleSharpness.Specification
import ThresholdHC.OracleSharpness.SignTest
import ThresholdHC.SharpRMS.WeakPopulation

/-! Passage from the finite-prefix deterministic-sign bound to randomized
estimators with unbounded stopping in the ordinary single-gap experiment. The
argument follows SharpRMS/WeakPopulation.lean, with the sign means one and
minus one in place of the three-bias design. Its private helpers are copied
here under the same names. -/
noncomputable section
namespace ThresholdHC.OracleSharpness
open MeasureTheory Filter Real Tier3 Tier4 Tier5 Tier6
open scoped ENNReal Topology

private def constantLaw (t : ℝ) (ht : |t| ≤ 1) : SignLaw :=
  ⟨fun _ => (1+t)/2, measurable_const, fun _ =>
    ⟨by linarith [(abs_le.mp ht).1], by linarith [(abs_le.mp ht).2]⟩⟩

private theorem seed_measurable {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (s t : ℝ) {n : ℕ} (f : R → Prefix n → ℝ) (hf : ∀ w, Measurable (fun u => f u w)) :
    Measurable (fun u => SharpRMS.prefixExpect (A.policy u) s t (f u)) := by
  apply Finset.measurable_sum
  intro w _
  exact (measurable_creationLaw A.policy A.policy_measurable _ _ (fun _ => measurable_const)
    (fun _ => measurable_const) w).mul (hf w)

private theorem seed_integrable {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : |t| ≤ 1) {n : ℕ}
    (f : R → Prefix n → ℝ) (hf : ∀ w, Measurable (fun u => f u w))
    (C : ℝ) (hC : ∀ u w, |f u w| ≤ C) :
    Integrable (fun u => SharpRMS.prefixExpect (A.policy u) s t (f u)) A.randomLaw := by
  apply (integrable_const C).mono' (seed_measurable A s t f hf).aestronglyMeasurable
  apply ae_of_all
  intro u
  let p := creationLaw (n := n) (A.policy u) (fun _=>s/2) (fun _=>(1+t)/2)
  have hp := creationLaw_total n (A.policy u) (fun _=>s/2) (fun _=>(1+t)/2)
    (fun _=>⟨by linarith, by linarith⟩)
    (fun _=>⟨by linarith [(abs_le.mp ht).1],by linarith [(abs_le.mp ht).2]⟩)
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
    ∫ u, SharpRMS.prefixExpect (A.policy u) (2*g.val) t (f u) ∂A.randomLaw := by
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
  unfold SharpRMS.prefixExpect
  rw [show 2*g.val/2 = g.val by ring]
  exact hr

/-- The deterministic-sign bound in the ordinary experiment at a point mass:
the two squared risks of a bounded statistic plus the flip price of the
uniform budget at the two sign laws are at least two. -/
private theorem population_sign_work {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (g : Gap) (hg : 2*g.val < 1) (B : ℝ) (hB : 0 ≤ B) (hb : UniformBudget (Measure.dirac g) A B)
    (X : R × ProcessTape → ℝ) (hm : Measurable X) (hx : ∀ z, |X z| ≤ 1) :
    let risk := fun (t : ℝ) (ht : |t| ≤ 1) =>
      ∫ z, (X (z.1.1,z.2)-t)^2 ∂experimentLaw (Measure.dirac g) A (constantLaw t ht)
    (2:ℝ) ≤ risk 1 (by norm_num) + risk (-1) (by norm_num) +
      2*g.val*artanh (2*g.val)*(2*B) := by
  let s := 2*g.val
  have hs : 0 < s := by dsimp [s]; linarith [g.property.1]
  let D := fun (t : ℝ) (ht : |t| ≤ 1) => experimentLaw (Measure.dirac g) A (constantLaw t ht)
  let loss := fun (t : ℝ) (z : PopulationSeed R × ProcessTape) => (X (z.1.1,z.2)-t)^2
  let LS := fun (n : ℕ) (t : ℝ) (u : R) (w : Prefix n) => (X (u,padPrefix n w)-t)^2
  let G := fun n t u => SharpRMS.prefixExpect (A.policy u) s t (LS n t u)
  let W := fun (n : ℕ) t u => SharpRMS.prefixExpect (A.policy u) s t (@workOf n)
  let price := s * artanh s
  have hprice : 0 ≤ price := mul_nonneg hs.le (artanh_nonneg hs.le)
  have hLm (t : ℝ) : Measurable (loss t) :=
    ((hm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).sub
      measurable_const).pow_const 2
  have bound (x t : ℝ) (h₁ : |x| ≤ 1) (h₂ : |t| ≤ 1) : |(x-t)^2| ≤ 4 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [mul_nonneg (show 0 ≤ 2-x+t by linarith [(abs_le.mp h₁).2,(abs_le.mp h₂).1])
      (show 0 ≤ 2+x-t by linarith [(abs_le.mp h₁).1,(abs_le.mp h₂).2])]
  have hLS (n) (t : ℝ) (w : Prefix n) : Measurable (fun u => LS n t u w) :=
    ((hm.comp (measurable_id.prodMk measurable_const)).sub measurable_const).pow_const 2
  have Gi n t (ht : |t| ≤ 1) : Integrable (G n t) A.randomLaw :=
    seed_integrable A s t hs.le hg.le ht _ (hLS n t) 4 (fun u w => bound _ _ (hx _) ht)
  have Wi n t (ht : |t| ≤ 1) : Integrable (W n t) A.randomLaw :=
    seed_integrable A s t hs.le hg.le ht _ (fun _ => measurable_const) n
      (fun u w => by rw [abs_of_nonneg (workOf_nonneg _)]; exact workOf_le_length _)
  have Wle n t (ht : |t| ≤ 1) : (∫ u, W n t u ∂A.randomLaw) ≤ B := by
    have he := dirac_prefix A g t ht (fun _ => @workOf n) (fun _ => measurable_const)
      ⟨(n:ℝ),fun u w => by rw [abs_of_nonneg (workOf_nonneg _)]; exact workOf_le_length _⟩
    exact he.ge.trans (SharpRMS.prefix_work_le A _ _ B hB hb n)
  have lim t (ht : |t| ≤ 1) : Tendsto (fun n => ∫ u, G n t u ∂A.randomLaw) atTop
      (𝓝 (∫ z, loss t z ∂D t ht)) := by
    have h := SharpRMS.limit_prefix A (Measure.dirac g) (constantLaw t ht) B hb (loss t) (hLm t) 4
      (fun z => bound _ _ (hx _) ht)
    apply h.congr
    intro n
    exact dirac_prefix A g t ht (LS n t) (hLS n t) ⟨4, fun u w => bound _ _ (hx _) ht⟩
  have hbnd (n : ℕ) : (2:ℝ) ≤ (∫ u, G n 1 u ∂A.randomLaw) +
      (∫ u, G n (-1) u ∂A.randomLaw) + price*(2*B) := by
    let H := fun u => G n 1 u + G n (-1) u + price*(W n 1 u + W n (-1) u)
    have hp := Gi n 1 (by norm_num)
    have hn := Gi n (-1) (by norm_num)
    have hw := ((Wi n 1 (by norm_num)).add (Wi n (-1) (by norm_num))).const_mul price
    have locally (u : R) : 2 ≤ H u := by
      have hh := prefix_sign_bound (A.policy u) s hs hg (fun w : Prefix n => X (u,padPrefix n w))
      simpa only [H,G,LS,W,sub_neg_eq_add] using hh
    have hpoint := integral_mono (μ := A.randomLaw) (integrable_const (2:ℝ))
      ((hp.add hn).add hw) locally
    have h₁ := integral_add (hp.add hn) hw
    simp only [Pi.add_apply] at hpoint h₁
    rw [h₁,integral_add hp hn,integral_const_mul,
      integral_add (Wi n 1 (by norm_num)) (Wi n (-1) (by norm_num))] at hpoint
    simp only [integral_const,probReal_univ,one_smul] at hpoint
    have w1 := mul_le_mul_of_nonneg_left (Wle n 1 (by norm_num)) hprice
    have w2 := mul_le_mul_of_nonneg_left (Wle n (-1) (by norm_num)) hprice
    linarith only [hpoint,w1,w2]
  have hlim := ((lim 1 (by norm_num)).add (lim (-1) (by norm_num))).add
    (tendsto_const_nhds (x := price*(2*B)))
  exact ge_of_tendsto hlim (Eventually.of_forall hbnd)

/-- The auxiliary ordinary-model bound: at a point mass with flip bias below
one, the single-gap minimax risk is at least c when the flip price of the
budget leaves room 1 - 4 c^2. -/
theorem small_gap_minimax_lower (g : Gap) (B c : ℝ) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hg : 2 * g.val < 1) (hbudget : 2 * g.val * Real.artanh (2 * g.val) * B ≤ 1 - 4 * c^2) :
    ENNReal.ofReal c ≤ minimaxRisk (Measure.dirac g) B := by
  apply le_sInf
  rintro _ ⟨R,mR,A,hb,rfl⟩
  by_contra! hsmall
  let μ := Measure.dirac g
  let X := fun z : R × ProcessTape => max (-1:ℝ) (min 1 (2*A.output z-1))
  have hm : Measurable X := by
    dsimp [X]
    exact measurable_const.max (measurable_const.min
      ((measurable_const.mul A.output_measurable).sub measurable_const))
  have hx (z) : |X z| ≤ 1 := abs_le.mpr ⟨le_max_left .., max_le (by norm_num) (min_le_left ..)⟩
  let risk := fun (t : ℝ) (ht : |t| ≤ 1) =>
    ∫ z, (X (z.1.1,z.2)-t)^2 ∂experimentLaw μ A (constantLaw t ht)
  have small (t : ℝ) (ht : |t| ≤ 1) : risk t ht < 4*c^2 := by
    let q := constantLaw t ht
    let P := experimentLaw μ A q
    let val := (1+t)/2
    have hav : signMean μ q.val = val := by simp [μ,q,constantLaw,signMean,val]
    have rms := (le_iSup (fun q' => rootMeanRisk (experimentLaw μ A q') (populationOutput A)
      (signMean μ q'.val)) q).trans_lt hsmall
    rw [hav] at rms
    have hsq : squaredRisk P (populationOutput A) val < ENNReal.ofReal (c^2) := by
      by_contra! hh
      have he := ENNReal.rpow_le_rpow hh (by norm_num : (0:ℝ) ≤ 1/2)
      rw [ofReal_square_rpow_half _ hc] at he
      exact (not_le_of_gt rms) he
    have hi : Integrable (fun z : PopulationSeed R × ProcessTape => (X (z.1.1,z.2)-t)^2) P := by
      have hmeas : Measurable (fun z : PopulationSeed R × ProcessTape => (X (z.1.1,z.2)-t)^2) :=
        ((hm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).sub
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
    have hcl : ENNReal.ofReal (risk t ht) ≤
        ENNReal.ofReal 4 * squaredRisk P (populationOutput A) val := by
      unfold risk
      rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _), squaredRisk,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_mono fun z =>
        (ENNReal.ofReal_le_ofReal (clip z)).trans_eq (ENNReal.ofReal_mul (by norm_num))
    have hh := hcl.trans_lt (ENNReal.mul_lt_mul_right
      (by norm_num : ENNReal.ofReal (4:ℝ) ≠ 0) ENNReal.ofReal_ne_top hsq)
    rw [← ENNReal.ofReal_mul (by norm_num)] at hh
    by_contra! hn
    exact (not_le_of_gt hh) (ENNReal.ofReal_le_ofReal hn)
  have hmain := population_sign_work A g hg B hB hb X hm hx
  change 2 ≤ risk 1 _ + risk (-1) _ + 2*g.val*artanh (2*g.val)*(2*B) at hmain
  linarith only [hmain,hbudget,small 1 (by norm_num),small (-1) (by norm_num)]

end ThresholdHC.OracleSharpness
