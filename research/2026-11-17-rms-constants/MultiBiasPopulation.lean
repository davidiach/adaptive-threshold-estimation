import MultiBiasPrefix
import SharpFourBudget

/-! Lift each finite likelihood inequality through the seed and stopping time.
All parameters use the same realization, work allowance and clipped output. -/
noncomputable section
namespace ThresholdHC.SharpRMS.MultiBias
open MeasureTheory Filter Real Tier3 Tier4 Tier5 Tier6 LargeBudget
open scoped ENNReal Topology unitInterval

def fraction (t : ℝ) (ht : |t|≤1) : unitInterval :=
  ⟨(1+t)/2,by constructor <;> linarith [(abs_le.mp ht).1,(abs_le.mp ht).2]⟩

def flat (p : unitInterval) : SignLaw := ⟨fun _ => p.val,measurable_const,fun _ => p.property⟩

def expectation {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (g : Gap) (p : unitInterval)
    (X : PopulationSeed R × ProcessTape → ℝ) (f : ℝ → ℝ) :=
  ∫ z, f (X z) ∂experimentLaw (Measure.dirac g) A (flat p)

theorem pair_cont (i : Fin 5) : Continuous (pair i) := by
  unfold pair
  apply Continuous.add
  all_goals
    apply Continuous.log _ (fun x => (test_pos ..).ne')
    unfold test
    fun_prop

private theorem output_bound {Ω : Type} (X : Ω → ℝ) (hx : ∀ z, |X z|≤1) (f : ℝ → ℝ) (hf : Continuous f) :
    ∃ C, ∀ z, |f (X z)|≤C := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s:=Set.Icc (-1:ℝ) 1) hf.continuousOn
  exact ⟨C,fun z => hC _ (abs_le.mp (hx z))⟩

theorem output_integrable {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hm : Measurable X) (hx : ∀ z, |X z|≤1) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable (fun z => f (X z)) P := by
  obtain ⟨C,hC⟩ := output_bound X hx f hf
  exact (integrable_const C).mono' (hf.measurable.comp hm).aestronglyMeasurable (ae_of_all _ hC)

theorem pair_population {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (g : Gap) (B : ℝ)
    (hb : UniformBudget (Measure.dirac g) A B) (hB : 0≤B) (hg : 2*g.val<1)
    (X : PopulationSeed R × ProcessTape → ℝ) (hm : Measurable X) (hx : ∀ z, |X z|≤1) (i : Fin 5) :
    expectation A g (fraction 0 (by norm_num)) X (pair i) ≤ charge (2*g.val) (bias i)*B +
      slope i*(expectation A g (fraction (bias i) (bias_lt i).le) X (fun x => (x-bias i)^2) +
               expectation A g (fraction (-bias i) (by simpa using (bias_lt i).le)) X (fun x => (x-(-bias i))^2)-2*target) := by
  let μ := Measure.dirac g
  let ν := populationSeedLaw μ A
  let p0 := fraction 0 (by norm_num)
  let p1 := fraction (bias i) (bias_lt i).le
  let p2 := fraction (-bias i) (by simpa using (bias_lt i).le)
  let loss := fun (t x : ℝ) => (x-t)^2
  let T := fun n (u : PopulationSeed R) (w : Prefix n) => X (padJoint n (u,w))
  let avg := fun (n : ℕ) (p : unitInterval) (F : PopulationSeed R → Prefix n → ℝ) (u : PopulationSeed R) =>
    priorExpect (populationPolicy A) populationGap (fun _ v w => F v w) (p,u)
  let W := fun n => avg n p0 (fun _ => @workOf n)
  let L := fun n p (f : ℝ → ℝ) => avg n p (fun u w => f (T n u w))
  have tm n (w : Prefix n) : Measurable (fun u => T n u w) :=
    (hm.comp (measurable_padJoint n)).comp (measurable_id.prodMk measurable_const)
  have ai n p (F : PopulationSeed R → Prefix n → ℝ) (mF : ∀ w, Measurable (fun u => F u w))
      (C : ℝ) (bF : ∀ u w, |F u w|≤C) : Integrable (avg n p F) ν := by
    have meas := measurable_priorExpect (populationPolicy A) (measurable_populationPolicy A)
      populationGap measurable_populationGap (fun _ v w => F v w) (fun w => (mF w).comp measurable_snd)
    apply (integrable_const C).mono' (meas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact ae_of_all _ fun u => priorExpect_bound (populationPolicy A) populationGap
      (fun v j => ⟨(v.2 j).property.1.le,(v.2 j).property.2⟩) _ C (fun _ => bF) (p,u)
  have li n p f (hf : Continuous f) : Integrable (L n p f) ν := by
    obtain ⟨C,hC⟩ := output_bound X hx f hf
    exact ai n p _ (fun w => hf.measurable.comp (tm n w)) C (fun _ _ => hC _)
  have wi n : Integrable (W n) ν := ai n p0 _ (fun _ => measurable_const) n
    (fun _ w => by rw [abs_of_nonneg (workOf_nonneg _)]; exact workOf_le_length w)
  have wle n : (∫ u, W n u ∂ν)≤B := population_prefix_work_budget μ A B hB hb n p0
  have lim p f (hf : Continuous f) : Tendsto (fun n => ∫ u, L n p f u ∂ν) atTop (𝓝 (expectation A g p X f)) := by
    obtain ⟨C,hC⟩ := output_bound X hx f hf
    apply (limit_prefix A μ (flat p) B hb (fun z => f (X z)) (hf.measurable.comp hm) C hC).congr
    intro n
    exact (population_realization R μ A (flat p)).2 n (fun u w => f (T n u w))
      (fun w => hf.measurable.comp (tm n w)) ⟨C,fun _ _ => hC _⟩
  have lc (t : ℝ) : Continuous (loss t) := by dsimp [loss]; fun_prop
  have ae : ∀ᵐ u ∂ν, u.2=fun _=>g := by
    dsimp [ν,μ,populationSeedLaw]
    rw [Measure.infinitePi_dirac,Measure.prod_dirac]
    exact (ae_map_iff (show Measurable (fun u : R => (u,fun _ : ℕ => g)) from
      measurable_id.prodMk measurable_const).aemeasurable (measurableSet_eq_fun measurable_snd measurable_const)).mpr
      (ae_of_all _ fun _ => rfl)
  let c := charge (2*g.val) (bias i)
  have hc : 0≤c := by
    have h : (2*g.val)^2<1 := by nlinarith [g.property.1,sq_nonneg (2*g.val-1),mul_pos (sub_pos.mpr hg) (show 0<1+2*g.val by linarith [g.property.1])]
    apply neg_nonneg.mpr (log_nonpos _ _)
    · nlinarith [(params i).2.1,mul_nonneg (show 0≤1-(bias i)^2 by linarith [(params i).2.1]) (sq_nonneg (2*g.val))]
    · nlinarith [mul_nonneg (sq_nonneg (bias i)) (sq_nonneg (2*g.val))]
  have finite_bound n : (∫ u, L n p0 (pair i) u ∂ν) ≤ c*B + slope i*(
      (∫ u, L n p1 (loss (bias i)) u ∂ν)+(∫ u, L n p2 (loss (-bias i)) u ∂ν)-2*target) := by
    let H := fun u => c*W n u+slope i*(L n p1 (loss (bias i)) u+L n p2 (loss (-bias i)) u-2*target)
    have a := li n p1 _ (lc (bias i))
    have b := li n p2 _ (lc (-bias i))
    have cost := (wi n).const_mul c
    have lr := ((a.add b).sub (integrable_const (2*target))).const_mul (slope i)
    have point : ∀ᵐ u ∂ν, L n p0 (pair i) u ≤ H u := by
      filter_upwards [ae] with u hu
      have gaps : populationGap u = fun _ => 2*g.val/2 := by funext j; simp [populationGap,hu]
      simpa only [L,avg,W,H,priorExpect,gaps,p0,p1,p2,fraction,prefixExpect,c,loss]
        using pair_prefix (populationPolicy A u) (2*g.val) (by linarith [g.property.1]) hg i (T n u)
    have h := integral_mono_ae (li n p0 _ (pair_cont i)) (cost.add lr) point
    change _ ≤ ∫ u, c*W n u+slope i*(_+_-2*target) ∂ν at h
    have split := integral_sub (a.add b) (integrable_const (μ:=ν) (2*target))
    simp only [Pi.add_apply,Pi.sub_apply] at lr split
    rw [integral_add cost lr,integral_const_mul,integral_const_mul,split,
      integral_add a b,integral_const,probReal_univ,one_smul] at h
    linarith only [h,mul_le_mul_of_nonneg_left (wle n) hc]
  exact le_of_tendsto_of_tendsto (lim p0 _ (pair_cont i))
    (tendsto_const_nhds.add (tendsto_const_nhds.mul (((lim p1 _ (lc _)).add (lim p2 _ (lc _))).sub tendsto_const_nhds)))
    (Eventually.of_forall finite_bound)

end ThresholdHC.SharpRMS.MultiBias
