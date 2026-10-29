import ThresholdHC.RareAboveTwo.BandError
import ThresholdHC.CriticalUpper.ScreenWork

/-! Work from the actual stopping time of the stage-dependent classifier. -/
noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal
section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {m : ℕ → Ω → ℝ}

theorem band_survival_positive (e : ℕ) (A₀ A₁ : ℕ → ℝ) (hA₁ : ∀ k, 0 ≤ A₁ k) (L k : ℕ)
    {d : ℝ} (hd : 0 < d) (ht : HasMeanTails μ m (1/2+d)) :
    μ.real {ω | k < bandStop e A₀ A₁ (fun j => m (e+j) ω) L} ≤
      (if cap (e+k)*d^2 ≤ 2*A₁ k then 1 else 0)+Real.exp (-(d^2/2*cap (e+k))) := by
  split_ifs with h
  · exact (measureReal_le_one (μ := μ)).trans (by linarith [Real.exp_pos (-(d^2/2*cap (e+k)))])
  · have hb := CriticalUpper.screenBoundary_lt_half (A₁ k) d (hA₁ k) hd (e+k) (lt_of_not_ge h)
    have hsub : {ω | k < bandStop e A₀ A₁ (fun j => m (e+j) ω) L} ⊆
        {ω | d/2 ≤ (1/2+d)-m (e+k) ω} := by
      intro ω hω
      have hs := (bandStop_min e A₀ A₁ (fun j => m (e+j) ω) L k hω).2.2
      change d/2 ≤ (1/2+d)-m (e+k) ω
      change _ ≤ _ at hs
      change CriticalUpper.screenBoundary (A₁ k) (e+k) < d/2 at hb
      change m (e+k) ω ≤ 1/2+CriticalUpper.screenBoundary (A₁ k) (e+k) at hs
      linarith
    have hp := (measureReal_mono hsub).trans (ht.lower (e+k) (d/2) (by positivity))
    have he : -2*cap (e+k)*(d/2)^2 = -(d^2/2*cap (e+k)) := by ring
    simpa only [he,zero_add] using hp

theorem band_survival_negative (e : ℕ) (A₀ A₁ : ℕ → ℝ) (hA₀ : ∀ k, 0 ≤ A₀ k) (L k : ℕ)
    {d : ℝ} (hd : 0 < d) (ht : HasMeanTails μ m (1/2-d)) :
    μ.real {ω | k < bandStop e A₀ A₁ (fun j => m (e+j) ω) L} ≤
      (if cap (e+k)*d^2 ≤ 2*A₀ k then 1 else 0)+Real.exp (-(d^2/2*cap (e+k))) := by
  split_ifs with h
  · exact (measureReal_le_one (μ := μ)).trans (by linarith [Real.exp_pos (-(d^2/2*cap (e+k)))])
  · have hb := CriticalUpper.screenBoundary_lt_half (A₀ k) d (hA₀ k) hd (e+k) (lt_of_not_ge h)
    have hsub : {ω | k < bandStop e A₀ A₁ (fun j => m (e+j) ω) L} ⊆
        {ω | d/2 ≤ m (e+k) ω-(1/2-d)} := by
      intro ω hω
      have hs := (bandStop_min e A₀ A₁ (fun j => m (e+j) ω) L k hω).2.1
      change d/2 ≤ m (e+k) ω-(1/2-d)
      change 1/2-CriticalUpper.screenBoundary (A₀ k) (e+k) ≤ m (e+k) ω at hs
      linarith
    have hp := (measureReal_mono hsub).trans (ht.upper (e+k) (d/2) (by positivity))
    have he : -2*cap (e+k)*(d/2)^2 = -(d^2/2*cap (e+k)) := by ring
    simpa only [he,zero_add] using hp

theorem measurable_bandWork (e : ℕ) (A₀ A₁ : ℕ → ℝ)
    (hm : ∀ k, Measurable (m k)) (L : ℕ) :
    Measurable (fun ω => cap (e+bandStop e A₀ A₁ (fun k => m k ω) L)) :=
  (measurable_of_countable (fun k => cap (e+k))).comp (measurable_bandStop e A₀ A₁ m hm L)

theorem integrable_bandWork (e : ℕ) (A₀ A₁ : ℕ → ℝ)
    (hm : ∀ k, Measurable (m k)) (L : ℕ) :
    Integrable (fun ω => cap (e+bandStop e A₀ A₁ (fun k => m k ω) L)) μ := by
  apply (integrable_const (cap (e+L))).mono' (measurable_bandWork e A₀ A₁ hm L).aestronglyMeasurable
  exact ae_of_all _ (fun ω => by
    rw [Real.norm_of_nonneg (cap_pos _).le]
    exact cap_mono (Nat.add_le_add_left (bandStop_le _ _ _ _ _) e))

theorem band_work_survival_identity (e : ℕ) (A₀ A₁ : ℕ → ℝ)
    (hm : ∀ k, Measurable (m k)) (L : ℕ) :
    (∫ ω, cap (e+bandStop e A₀ A₁ (fun k => m k ω) L) ∂μ) =
      cap e+∑ k ∈ Finset.range L, cap (e+k)*μ.real {ω | k < bandStop e A₀ A₁ (fun j => m j ω) L} := by
  let f : ℕ → Ω → ℝ := fun k =>
    {ω | k < bandStop e A₀ A₁ (fun j => m j ω) L}.indicator (fun _ => cap (e+k))
  have hs (k : ℕ) : MeasurableSet {ω | k < bandStop e A₀ A₁ (fun j => m j ω) L} :=
    measurableSet_lt measurable_const (measurable_bandStop e A₀ A₁ m hm L)
  have hf (k : ℕ) : Integrable (f k) μ := (integrable_const _).indicator (hs k)
  have he : (fun ω => cap (e+bandStop e A₀ A₁ (fun k => m k ω) L)) =
      fun ω => cap e+∑ k ∈ Finset.range L, f k ω := by
    funext ω
    have h := dyadic_survival_identity (bandStop e A₀ A₁ (fun k => m k ω) L) L (bandStop_le _ _ _ _ _)
    have hmul := congrArg (fun x : ℝ => cap e*x) h
    simp only [mul_add,mul_one,Finset.mul_sum] at hmul
    change cap e*cap (bandStop e A₀ A₁ (fun k => m k ω) L) = _ at hmul
    rw [show cap (e+bandStop e A₀ A₁ (fun k => m k ω) L) =
      cap e*cap (bandStop e A₀ A₁ (fun k => m k ω) L) by simp [cap,pow_add],hmul]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : k < bandStop e A₀ A₁ (fun k => m k ω) L <;> simp [f,h,cap,pow_add]
  rw [he,integral_add (integrable_const _) (integrable_finsetSum _ (fun k _ => hf k)),
    integral_finsetSum _ (fun k _ => hf k)]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simpa [f,mul_comm] using integral_indicator_const (cap (e+k)) (hs k)

end
end ThresholdHC.RareAboveTwo
