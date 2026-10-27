import ThresholdHC.Tier5.FiniteEnvironment

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace ThresholdHC.Tier5

def FiniteKernelRealization {Seed A : Type} [MeasurableSpace Seed] [MeasurableSpace A]
    [Fintype A] (μ : Measure Seed) (P : Measure (Seed × A)) (p : Seed → A → ℝ) : Prop :=
  ∀ (f : Seed × A → ℝ), Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    (∫ x, f x ∂P) = ∫ u, ∑ a, p u a * f (u,a) ∂μ

theorem finite_kernel_kl_identity {Seed A : Type} [MeasurableSpace Seed]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure Seed) (P Q : Measure (Seed × A))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p q : Seed → A → ℝ)
    (hpm : ∀ a, Measurable (fun u => p u a))
    (hqm : ∀ a, Measurable (fun u => q u a))
    (hp0 : ∀ u a, 0 ≤ p u a) (hq0 : ∀ u a, 0 ≤ q u a)
    (K : ℝ) (hK : 0 ≤ K)
    (hpq : ∀ u a, p u a ≤ K * q u a) (hqp : ∀ u a, q u a ≤ K * p u a)
    (hP : FiniteKernelRealization μ P p) (hQ : FiniteKernelRealization μ Q q) :
    klDiv P Q = ENNReal.ofReal (∫ u, klFT (p u) (q u) ∂μ) := by
  let r : Seed × A → ℝ := fun x => p x.1 x.2 / q x.1 x.2
  have hrm : Measurable r :=
    (measurable_from_prod_countable_left hpm).div (measurable_from_prod_countable_left hqm)
  have hr0 (x : Seed × A) : 0 ≤ r x := div_nonneg (hp0 _ _) (hq0 _ _)
  have hrbound (x : Seed × A) : |r x| ≤ K := by
    rw [abs_of_nonneg (hr0 x)]
    exact ratio_le_of_comparison (hq0 _ _) hK (hpq _ _)
  have hlog (x : Seed × A) : |Real.log (r x)| ≤ K :=
    abs_log_ratio_le (hp0 _ _) (hq0 _ _) hK (hpq _ _) (hqp _ _)
  have hratio (u : Seed) (a : A) : q u a * r (u,a) = p u a := by
    dsimp [r]
    by_cases hz : q u a = 0
    · have hzero : p u a = 0 := le_antisymm (by simpa [hz] using hpq u a) (hp0 u a)
      simp [hz, hzero]
    · exact mul_div_cancel₀ _ hz
  have hdensity : Q.withDensity (fun x => ENNReal.ofReal (r x)) = P := by
    symm
    apply Tier4.measure_eq_withDensity_of_setIntegral P Q r
      (integrable_of_abs_bound Q r hrm K hrbound) hr0
    intro s hs
    let f : Seed × A → ℝ := s.indicator 1
    have hfm : Measurable f := measurable_const.indicator hs
    have hfb (x : Seed × A) : |f x| ≤ 1 := by
      by_cases hx : x ∈ s <;> simp [f, hx]
    have hpf := hP f hfm ⟨1,hfb⟩
    have hqf := hQ (fun x => r x * f x) (hrm.mul hfm) ⟨K, fun x => by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hfb x) (abs_nonneg _)).trans (by simpa using hrbound x)⟩
    calc
      P.real s = ∫ x, f x ∂P := (integral_indicator_one hs).symm
      _ = ∫ u, ∑ a, p u a * f (u,a) ∂μ := hpf
      _ = ∫ u, ∑ a, q u a * (r (u,a) * f (u,a)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with u
        apply Finset.sum_congr rfl
        intro a ha
        rw [← mul_assoc, hratio]
      _ = ∫ x, r x * f x ∂Q := hqf.symm
      _ = ∫ x in s, r x ∂Q := by
        rw [← integral_indicator hs]
        congr 1
        funext x
        by_cases hx : x ∈ s <;> simp [f, hx]
  rw [klDiv_of_bounded_likelihood P Q r hrm hr0 K hlog hdensity]
  congr 1
  exact hP (fun x => Real.log (r x)) hrm.log ⟨K,hlog⟩

theorem integrable_kernel_kl {Seed A : Type} [MeasurableSpace Seed] [Fintype A]
    (μ : Measure Seed) [IsFiniteMeasure μ] (p q : Seed → A → ℝ)
    (hpm : ∀ a, Measurable (fun u => p u a))
    (hqm : ∀ a, Measurable (fun u => q u a))
    (hp0 : ∀ u a, 0 ≤ p u a) (hp1 : ∀ u a, p u a ≤ 1)
    (hq0 : ∀ u a, 0 ≤ q u a) (K : ℝ) (hK : 0 ≤ K)
    (hpq : ∀ u a, p u a ≤ K * q u a) (hqp : ∀ u a, q u a ≤ K * p u a) :
    Integrable (fun u => klFT (p u) (q u)) μ := by
  unfold klFT
  apply integrable_finsetSum
  intro a ha
  apply integrable_of_abs_bound μ _ ((hpm a).mul ((hpm a).div (hqm a)).log) K
  intro u
  change |p u a * Real.log (p u a / q u a)| ≤ K
  rw [abs_mul, abs_of_nonneg (hp0 u a)]
  exact (mul_le_mul_of_nonneg_right (hp1 u a) (abs_nonneg _)).trans (by
    simpa using abs_log_ratio_le (hp0 u a) (hq0 u a) hK (hpq u a) (hqp u a))

theorem integrable_kernel_work {Seed A : Type} [MeasurableSpace Seed] [Fintype A]
    (μ : Measure Seed) [IsFiniteMeasure μ] (p : Seed → A → ℝ)
    (hpm : ∀ a, Measurable (fun u => p u a))
    (hp0 : ∀ u a, 0 ≤ p u a) (hp1 : ∀ u a, p u a ≤ 1) (w : A → ℝ) :
    Integrable (fun u => ∑ a, p u a * w a) μ := by
  apply integrable_finsetSum
  intro a ha
  apply integrable_of_abs_bound μ _ ((hpm a).mul_const (w a)) |w a|
  intro u
  change |p u a * w a| ≤ |w a|
  rw [abs_mul, abs_of_nonneg (hp0 u a)]
  simpa using mul_le_mul_of_nonneg_right (hp1 u a) (abs_nonneg (w a))

theorem finite_kernel_kl_bound {Seed A : Type} [MeasurableSpace Seed]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure Seed) [IsFiniteMeasure μ] (P Q : Measure (Seed × A))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p q : Seed → A → ℝ)
    (hpm : ∀ a, Measurable (fun u => p u a))
    (hqm : ∀ a, Measurable (fun u => q u a))
    (hp0 : ∀ u a, 0 ≤ p u a) (hp1 : ∀ u a, p u a ≤ 1)
    (hq0 : ∀ u a, 0 ≤ q u a) (K : ℝ) (hK : 0 ≤ K)
    (hpq : ∀ u a, p u a ≤ K * q u a) (hqp : ∀ u a, q u a ≤ K * p u a)
    (hP : FiniteKernelRealization μ P p) (hQ : FiniteKernelRealization μ Q q)
    (w : A → ℝ) (C : ℝ)
    (hpoint : ∀ u, klFT (p u) (q u) ≤ C * ∑ a, p u a * w a) :
    klDiv P Q ≤ ENNReal.ofReal (C * ∫ u, ∑ a, p u a * w a ∂μ) := by
  rw [finite_kernel_kl_identity μ P Q p q hpm hqm hp0 hq0 K hK hpq hqp hP hQ]
  apply ENNReal.ofReal_le_ofReal
  have hint := integral_mono
    (integrable_kernel_kl μ p q hpm hqm hp0 hp1 hq0 K hK hpq hqp)
    ((integrable_kernel_work μ p hpm hp0 hp1 w).const_mul C) hpoint
  simpa only [integral_const_mul] using hint

end ThresholdHC.Tier5
