import ThresholdHC.CriticalEntropy.FiniteAffinity
import ThresholdHC.Tier5.FiniteJoint

noncomputable section

namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The existing bounded-test-function realization determines the whole joint
seed and finite-output law, including zero-probability output cells. -/
theorem finite_kernel_density {R I : Type} [MeasurableSpace R]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure R) [IsFiniteMeasure ν] (P : Measure (R × I)) [IsFiniteMeasure P]
    (p : R → I → ℝ) (hpm : ∀ i, Measurable (fun r => p r i))
    (hp0 : ∀ r i, 0 ≤ p r i) (hp1 : ∀ r i, p r i ≤ 1)
    (hP : Tier5.FiniteKernelRealization ν P p) :
    P = (ν.prod Measure.count).withDensity (fun z => ENNReal.ofReal (p z.1 z.2)) := by
  let ξ := ν.prod (Measure.count : Measure I)
  have hm : Measurable (fun z : R × I => p z.1 z.2) :=
    measurable_from_prod_countable_left hpm
  have hi : Integrable (fun z : R × I => p z.1 z.2) ξ :=
    Tier5.integrable_of_abs_bound ξ _ hm 1
      (fun z => by rw [abs_of_nonneg (hp0 _ _)]; exact hp1 _ _)
  apply Tier4.measure_eq_withDensity_of_setIntegral P ξ _ hi (fun z => hp0 _ _)
  intro S hS
  let f : R × I → ℝ := S.indicator (fun _ => 1)
  have hfm : Measurable f := measurable_const.indicator hS
  have hfb (z : R × I) : |f z| ≤ 1 := by by_cases hz : z ∈ S <;> simp [f,hz]
  have hif : Integrable (fun z : R × I => p z.1 z.2*f z) ξ :=
    Tier5.integrable_of_abs_bound ξ _ (hm.mul hfm) 1 (fun z => by
      rw [abs_mul,abs_of_nonneg (hp0 _ _)]
      exact (mul_le_mul_of_nonneg_left (hfb z) (hp0 _ _)).trans (by simpa using hp1 z.1 z.2))
  calc
    P.real S = ∫ z, f z ∂P := (integral_indicator_one hS).symm
    _ = ∫ r, ∑ i, p r i*f (r,i) ∂ν := hP f hfm ⟨1,hfb⟩
    _ = ∫ r, ∫ i, p r i*f (r,i) ∂Measure.count ∂ν := by simp [integral_fintype]
    _ = ∫ z, p z.1 z.2*f z ∂ξ := (integral_prod _ hif).symm
    _ = ∫ z in S, p z.1 z.2 ∂ξ := by
      rw [← integral_indicator hS]
      congr 1
      funext z
      by_cases hz : z ∈ S <;> simp [f,hz]

theorem finite_kernel_hellinger_identity {R I : Type} [MeasurableSpace R]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure R) [IsFiniteMeasure ν] (P Q : Measure (R × I))
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (p q : R → I → ℝ)
    (hpm : ∀ i, Measurable (fun r => p r i)) (hqm : ∀ i, Measurable (fun r => q r i))
    (hp0 : ∀ r i, 0 ≤ p r i) (hp1 : ∀ r i, p r i ≤ 1)
    (hq0 : ∀ r i, 0 ≤ q r i) (hq1 : ∀ r i, q r i ≤ 1)
    (hP : Tier5.FiniteKernelRealization ν P p) (hQ : Tier5.FiniteKernelRealization ν Q q) :
    (hellingerAffinity P Q).toReal = ∫ r, realFiniteAffinity (p r) (q r) ∂ν := by
  have hpe : Measurable (fun z : R × I => ENNReal.ofReal (p z.1 z.2)) :=
    (measurable_from_prod_countable_left hpm).ennreal_ofReal
  have hqe : Measurable (fun z : R × I => ENNReal.ofReal (q z.1 z.2)) :=
    (measurable_from_prod_countable_left hqm).ennreal_ofReal
  rw [finite_kernel_density ν P p hpm hp0 hp1 hP,finite_kernel_density ν Q q hqm hq0 hq1 hQ,
    hellingerAffinity_revealed_finite ν _ _ hpe hqe (fun _ => ENNReal.ofReal_ne_top)
      (fun _ => ENNReal.ofReal_ne_top)]
  have hm : Measurable (fun r => finiteAffinity (fun i => ENNReal.ofReal (p r i))
      (fun i => ENNReal.ofReal (q r i))) := by
    unfold finiteAffinity
    fun_prop
  have hfin (r) : finiteAffinity (fun i => ENNReal.ofReal (p r i))
      (fun i => ENNReal.ofReal (q r i)) < ∞ := by
    unfold finiteAffinity
    apply ENNReal.sum_lt_top.mpr
    intro i hi
    exact lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
  rw [← integral_toReal hm.aemeasurable (ae_of_all _ hfin)]
  apply integral_congr_ae
  exact ae_of_all _ (fun r => by
    dsimp only
    rw [finiteAffinity_toReal (fun i => ENNReal.ofReal (p r i))
      (fun i => ENNReal.ofReal (q r i)) (fun _ => ENNReal.ofReal_ne_top) (fun _ => ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal,hp0,hq0])

/-- A pointwise conditional affinity/work bound integrates over an arbitrary
measurable seed law while retaining the seed in the observation. -/
theorem finite_kernel_hellinger_bound {R I : Type} [MeasurableSpace R]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure R) [IsProbabilityMeasure ν] (P Q : Measure (R × I))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (p q : R → I → ℝ)
    (hpm : ∀ i, Measurable (fun r => p r i)) (hqm : ∀ i, Measurable (fun r => q r i))
    (hp0 : ∀ r i, 0 ≤ p r i) (hq0 : ∀ r i, 0 ≤ q r i)
    (hpn : ∀ r, ∑ i, p r i = 1) (hqn : ∀ r, ∑ i, q r i = 1)
    (hP : Tier5.FiniteKernelRealization ν P p) (hQ : Tier5.FiniteKernelRealization ν Q q)
    (W : R → ℝ) (hW : Integrable W ν) (K c : ℝ)
    (hpoint : ∀ r, (1-realFiniteAffinity (p r) (q r))*K ≤ c*W r) :
    (1-(hellingerAffinity P Q).toReal)*K ≤ c*∫ r, W r ∂ν := by
  have hp1 (r i) : p r i ≤ 1 := by
    rw [← hpn r]
    exact Finset.single_le_sum (fun j hj => hp0 r j) (Finset.mem_univ i)
  have hq1 (r i) : q r i ≤ 1 := by
    rw [← hqn r]
    exact Finset.single_le_sum (fun j hj => hq0 r j) (Finset.mem_univ i)
  have hm : Measurable (fun r => realFiniteAffinity (p r) (q r)) := by
    unfold realFiniteAffinity
    fun_prop
  have hi : Integrable (fun r => realFiniteAffinity (p r) (q r)) ν :=
    Tier5.integrable_of_abs_bound ν _ hm 1 (fun r => by
      have hn : 0 ≤ realFiniteAffinity (p r) (q r) :=
        Finset.sum_nonneg (fun i hi => Real.sqrt_nonneg _)
      rw [abs_of_nonneg hn]
      exact realFiniteAffinity_le_one _ _ (hp0 r) (hq0 r) (hpn r) (hqn r))
  rw [finite_kernel_hellinger_identity ν P Q p q hpm hqm hp0 hp1 hq0 hq1 hP hQ]
  calc
    _ = ∫ r, (1-realFiniteAffinity (p r) (q r))*K ∂ν := by
      rw [integral_mul_const,integral_sub (integrable_const 1) hi]
      simp
    _ ≤ ∫ r, c*W r ∂ν := integral_mono
      (((integrable_const 1).sub hi).mul_const K) (hW.const_mul c) hpoint
    _ = _ := integral_const_mul _ _

/-- Integrating out an independent latent environment gives the correct finite
kernel on the observable seed, without revealing any environment coordinate. -/
theorem finite_kernel_marginal {R D I : Type}
    [MeasurableSpace R] [MeasurableSpace D] [MeasurableSpace I] [Fintype I]
    (ν : Measure R) [IsFiniteMeasure ν] (μ : Measure D) [IsFiniteMeasure μ]
    (P : Measure ((R × D) × I)) (p : (R × D) → I → ℝ)
    (hpm : ∀ i, Measurable (fun z => p z i))
    (hp0 : ∀ z i, 0 ≤ p z i) (hp1 : ∀ z i, p z i ≤ 1)
    (hP : Tier5.FiniteKernelRealization (ν.prod μ) P p) :
    Tier5.FiniteKernelRealization ν (P.map (fun z => (z.1.1,z.2)))
      (fun r i => ∫ d, p (r,d) i ∂μ) := by
  intro f hf hb
  obtain ⟨C,hC⟩ := hb
  have hproj : Measurable (fun z : (R × D) × I => (z.1.1,z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hif (i) : Integrable (fun z : R × D => p z i*f (z.1,i)) (ν.prod μ) := by
    apply Tier5.integrable_of_abs_bound (ν.prod μ) _
      ((hpm i).mul (hf.comp (measurable_fst.prodMk measurable_const))) C
    intro z
    change |p z i*f (z.1,i)| ≤ C
    rw [abs_mul,abs_of_nonneg (hp0 z i)]
    exact (mul_le_mul_of_nonneg_right (hp1 z i) (abs_nonneg _)).trans (by simpa using hC (z.1,i))
  have hif' (r i) : Integrable (fun d => p (r,d) i*f (r,i)) μ := by
    apply Tier5.integrable_of_abs_bound μ _
      (((hpm i).comp (measurable_const.prodMk measurable_id)).mul_const _) |f (r,i)|
    intro d
    change |p (r,d) i*f (r,i)| ≤ |f (r,i)|
    rw [abs_mul,abs_of_nonneg (hp0 (r,d) i)]
    simpa using mul_le_mul_of_nonneg_right (hp1 (r,d) i) (abs_nonneg (f (r,i)))
  rw [integral_map hproj.aemeasurable hf.aestronglyMeasurable]
  calc
    _ = ∫ z, ∑ i, p z i*f (z.1,i) ∂ν.prod μ :=
      hP _ (hf.comp hproj) ⟨C,fun z => hC (z.1.1,z.2)⟩
    _ = ∫ r, ∫ d, ∑ i, p (r,d) i*f (r,i) ∂μ ∂ν :=
      integral_prod _ (integrable_finsetSum _ (fun i hi => hif i))
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun r => by
        dsimp only
        rw [integral_finsetSum _ (fun i hi => hif' r i)]
        simp only [integral_mul_const])

end ThresholdHC.CriticalEntropy
