import ThresholdHC.CriticalUpper.ScreenError

/-! Expected work from the dyadic survival sum. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal

theorem screenBoundary_lt_half (A d : ℝ) (hA : 0 ≤ A) (hd : 0 < d) (k : ℕ)
    (h : 2*A < cap k*d^2) : screenBoundary A k < d/2 := by
  have hb := screenBoundary_nonneg A k
  have hs : 2*cap k*(screenBoundary A k)^2 = A := by
    rw [screenBoundary_sq A hA k]
    field_simp [(cap_pos k).ne']
  by_contra hn
  have hsq : d^2 ≤ 4*(screenBoundary A k)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq (cap_pos k).le
  nlinarith

section ScreenWork
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {m : ℕ → Ω → ℝ}

theorem screen_survival_positive (A₀ A₁ : ℝ) (hA₁ : 0 ≤ A₁) (L k : ℕ)
    {d : ℝ} (hd : 0 < d) (ht : HasMeanTails μ m (1/2+d)) :
    μ.real {ω | k < screenStop A₀ A₁ (fun j => m j ω) L} ≤
      (if cap k*d^2 ≤ 2*A₁ then 1 else 0)+Real.exp (-(d^2/2*cap k)) := by
  split_ifs with h
  · exact (measureReal_le_one (μ := μ)).trans (by linarith [Real.exp_pos (-(d^2/2*cap k))])
  · have hb := screenBoundary_lt_half A₁ d hA₁ hd k (lt_of_not_ge h)
    have hsub : {ω | k < screenStop A₀ A₁ (fun j => m j ω) L} ⊆
        {ω | d/2 ≤ (1/2+d)-m k ω} := by
      intro ω hω
      have hs := (screenStop_min A₀ A₁ (fun j => m j ω) L k hω).2.2
      change d/2 ≤ (1/2+d)-m k ω
      linarith
    have hp := (measureReal_mono hsub).trans (ht.lower k (d/2) (by positivity))
    have he : -2*cap k*(d/2)^2 = -(d^2/2*cap k) := by ring
    simpa only [he,zero_add] using hp

theorem screen_survival_negative (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (L k : ℕ)
    {d : ℝ} (hd : 0 < d) (ht : HasMeanTails μ m (1/2-d)) :
    μ.real {ω | k < screenStop A₀ A₁ (fun j => m j ω) L} ≤
      (if cap k*d^2 ≤ 2*A₀ then 1 else 0)+Real.exp (-(d^2/2*cap k)) := by
  split_ifs with h
  · exact (measureReal_le_one (μ := μ)).trans (by linarith [Real.exp_pos (-(d^2/2*cap k))])
  · have hb := screenBoundary_lt_half A₀ d hA₀ hd k (lt_of_not_ge h)
    have hsub : {ω | k < screenStop A₀ A₁ (fun j => m j ω) L} ⊆
        {ω | d/2 ≤ m k ω-(1/2-d)} := by
      intro ω hω
      have hs := (screenStop_min A₀ A₁ (fun j => m j ω) L k hω).2.1
      change d/2 ≤ m k ω-(1/2-d)
      linarith
    have hp := (measureReal_mono hsub).trans (ht.upper k (d/2) (by positivity))
    have he : -2*cap k*(d/2)^2 = -(d^2/2*cap k) := by ring
    simpa only [he,zero_add] using hp

theorem measurable_screenWork (A₀ A₁ : ℝ) (hm : ∀ k, Measurable (m k)) (L : ℕ) :
    Measurable (fun ω => cap (screenStop A₀ A₁ (fun k => m k ω) L)) :=
  (measurable_of_countable cap).comp (measurable_screenStop A₀ A₁ m hm L)

theorem integrable_screenWork (A₀ A₁ : ℝ) (hm : ∀ k, Measurable (m k)) (L : ℕ) :
    Integrable (fun ω => cap (screenStop A₀ A₁ (fun k => m k ω) L)) μ := by
  apply (integrable_const (cap L)).mono' (measurable_screenWork A₀ A₁ hm L).aestronglyMeasurable
  exact ae_of_all _ (fun ω => by rw [Real.norm_of_nonneg (cap_pos _).le]; exact cap_mono (screenStop_le _ _ _ _))

theorem screen_expected_work_le_cap (A₀ A₁ : ℝ) (hm : ∀ k, Measurable (m k)) (L : ℕ) :
    (∫ ω, cap (screenStop A₀ A₁ (fun k => m k ω) L) ∂μ) ≤ cap L := by
  calc
    _ ≤ ∫ _ : Ω, cap L ∂μ := integral_mono (integrable_screenWork A₀ A₁ hm L) (integrable_const _)
      (fun ω => cap_mono (screenStop_le _ _ _ _))
    _ = _ := by simp

theorem screen_work_survival_identity (A₀ A₁ : ℝ) (hm : ∀ k, Measurable (m k)) (L : ℕ) :
    (∫ ω, cap (screenStop A₀ A₁ (fun k => m k ω) L) ∂μ) =
      1+∑ k ∈ Finset.range L, cap k*μ.real {ω | k < screenStop A₀ A₁ (fun j => m j ω) L} := by
  let f : ℕ → Ω → ℝ := fun k =>
    {ω | k < screenStop A₀ A₁ (fun j => m j ω) L}.indicator (fun _ => cap k)
  have hs (k : ℕ) : MeasurableSet {ω | k < screenStop A₀ A₁ (fun j => m j ω) L} :=
    measurableSet_lt measurable_const (measurable_screenStop A₀ A₁ m hm L)
  have hf (k : ℕ) : Integrable (f k) μ := (integrable_const _).indicator (hs k)
  have he : (fun ω => cap (screenStop A₀ A₁ (fun k => m k ω) L)) =
      fun ω => 1+∑ k ∈ Finset.range L, f k ω := by
    funext ω
    rw [show cap (screenStop A₀ A₁ (fun k => m k ω) L) = _ from
      dyadic_survival_identity _ L (screenStop_le _ _ _ _)]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : k < screenStop A₀ A₁ (fun j => m j ω) L <;> simp [f,h,cap]
  rw [he,integral_add (integrable_const _) (integrable_finsetSum _ (fun k _ => hf k)),
    integral_finsetSum _ (fun k _ => hf k)]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simpa [f,mul_comm] using integral_indicator_const (cap k) (hs k)

theorem screen_work_bound_of_survival (A₀ A₁ A : ℝ) (hA : 1 ≤ A)
    (hm : ∀ k, Measurable (m k)) (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1/2)
    (hs : ∀ k, μ.real {ω | k < screenStop A₀ A₁ (fun j => m j ω) L} ≤
      (if cap k*d^2 ≤ 2*A then 1 else 0)+Real.exp (-(d^2/2*cap k))) :
    (∫ ω, cap (screenStop A₀ A₁ (fun k => m k ω) L) ∂μ) ≤ min (cap L) (10*A/d^2) := by
  refine le_min (screen_expected_work_le_cap A₀ A₁ hm L) ?_
  have hI : (∑ k ∈ Finset.range L, cap k*(if cap k*d^2 ≤ 2*A then 1 else 0)) ≤ 4*A/d^2 := by
    calc
      _ = ∑ k ∈ Finset.range L, if cap k*d^2 ≤ 2*A then cap k else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        split_ifs <;> simp
      _ ≤ 2*(2*A)/d^2 := finite_dyadic_scaled_indicator_sum L d (2*A) hd (by positivity)
      _ = _ := by ring
  have hE : (∑ k ∈ Finset.range L, cap k*Real.exp (-(d^2/2*cap k))) ≤ 4/d^2 := by
    have h := finite_dyadic_sum_v1 (d^2/2) (by positivity) L
    convert h using 1; field_simp; norm_num
  have hb : (∫ ω, cap (screenStop A₀ A₁ (fun k => m k ω) L) ∂μ) ≤ 1+4*A/d^2+4/d^2 := by
    rw [screen_work_survival_identity A₀ A₁ hm L]
    have hsum := Finset.sum_le_sum (s := Finset.range L)
      (fun k _ => mul_le_mul_of_nonneg_left (hs k) (cap_pos k).le)
    simp_rw [mul_add,Finset.sum_add_distrib] at hsum
    linarith
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg d)
  have he : (1+4*A/d^2+4/d^2)*d^2 = d^2+4*A+4 := by field_simp
  rw [he] at hm
  nlinarith

theorem screen_work_positive (A₀ A₁ : ℝ) (hA₁ : 1 ≤ A₁) (L : ℕ)
    {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1/2) (ht : HasMeanTails μ m (1/2+d)) :
    (∫ ω, cap (screenStop A₀ A₁ (fun k => m k ω) L) ∂μ) ≤ min (cap L) (10*A₁/d^2) :=
  screen_work_bound_of_survival A₀ A₁ A₁ hA₁ ht.measurable L hd hdmax
    (fun k => screen_survival_positive A₀ A₁ (by linarith) L k hd ht)

theorem screen_work_negative (A₀ A₁ : ℝ) (hA₀ : 1 ≤ A₀) (L : ℕ)
    {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1/2) (ht : HasMeanTails μ m (1/2-d)) :
    (∫ ω, cap (screenStop A₀ A₁ (fun k => m k ω) L) ∂μ) ≤ min (cap L) (10*A₀/d^2) :=
  screen_work_bound_of_survival A₀ A₁ A₀ hA₀ ht.measurable L hd hdmax
    (fun k => screen_survival_negative A₀ A₁ (by linarith) L k hd ht)

end ScreenWork

end ThresholdHC.CriticalUpper
