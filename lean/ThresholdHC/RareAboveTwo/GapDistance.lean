import ThresholdHC.RareAboveTwo.GapKernel

noncomputable section
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Tier6
open MeasureTheory ThresholdHC.Proofs ThresholdHC.Proofs.Transcript ThresholdHC.CriticalEntropy

theorem gap_sign_distance {m n : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (pol : List Bool → Option (Fin m)) (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j ∧ q j ≤ 1)
    (i : Fin m) (a : ℝ) (ha : a ≤ 1/2) (hsupp : ∀ᵐ d : Gap ∂μ, (d : ℝ) ≤ a) :
    2*(1-realFiniteAffinity (gapMixture (n := n) μ pol (Function.update q i 0))
      (gapMixture μ pol (Function.update q i 1))) ≤
      32*a^2*(∑ w : Fin n → Option Bool, gapMixture μ pol (Function.update q i 0) w*coinWork pol i w) := by
  classical
  let η := Measure.pi (fun _ : Fin m => μ)
  let q₀ := Function.update q i 0
  let q₁ := Function.update q i 1
  have hq₀ := update_range q hq i 0 (by norm_num)
  have hq₁ := update_range q hq i 1 (by norm_num)
  have hP (x) := gapKernel_total (n := n) pol q₀ hq₀ x
  have hQ (x) := gapKernel_total (n := n) pol q₁ hq₁ x
  have hJ := finite_distance_integral_le η (gapKernel (n := n) pol q₀) (gapKernel (n := n) pol q₁)
    (gapKernel_measurable pol q₀) (gapKernel_measurable pol q₁)
    (fun x => (hP x).1) (fun x => (hQ x).1) (fun x => (hP x).2) (fun x => (hQ x).2)
  have hD := finite_distance_integrable η (gapKernel (n := n) pol q₀) (gapKernel (n := n) pol q₁)
    (gapKernel_measurable pol q₀) (gapKernel_measurable pol q₁)
    (fun x => (hP x).1) (fun x => (hQ x).1) (fun x => (hP x).2) (fun x => (hQ x).2)
  have hiw (w : Fin n → Option Bool) := (gapKernel_integrable μ pol q₀ hq₀ w).mul_const (coinWork pol i w)
  have hW := integrable_finsetSum Finset.univ (fun w _ => hiw w)
  have hb : ∀ᵐ x : Fin m → Gap ∂η,
      2*(1-realFiniteAffinity (gapKernel (n := n) pol q₀ x) (gapKernel (n := n) pol q₁ x)) ≤
      32*a^2*(∑ w : Fin n → Option Bool, gapKernel (n := n) pol q₀ x w*coinWork pol i w) := by
    have he : ∀ᵐ x : Fin m → Gap ∂η, (x i : ℝ) ≤ a := (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin m => μ) (i := i)).eventually hsupp
    filter_upwards [he] with x hx
    exact transcript_sign_distance pol (fun j => (x j : ℝ)) q i a
      (fun j => (x j).property) hq hx ha
  calc
    _ ≤ 2*(∫ x, 1-realFiniteAffinity (gapKernel (n := n) pol q₀ x) (gapKernel (n := n) pol q₁ x) ∂η) := by
      change 2*(1-realFiniteAffinity (fun w => ∫ x, gapKernel (n := n) pol q₀ x w ∂η)
        (fun w => ∫ x, gapKernel (n := n) pol q₁ x w ∂η)) ≤ _
      linarith
    _ = ∫ x, 2*(1-realFiniteAffinity (gapKernel (n := n) pol q₀ x) (gapKernel (n := n) pol q₁ x)) ∂η := (integral_const_mul _ _).symm
    _ ≤ ∫ x, 32*a^2*(∑ w : Fin n → Option Bool, gapKernel (n := n) pol q₀ x w*coinWork pol i w) ∂η :=
      integral_mono_ae (hD.const_mul 2) (hW.const_mul _) hb
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum _ (fun w _ => hiw w)]
      simp only [integral_mul_const]
      rfl

theorem gap_rare_distance {m n : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (pol : List Bool → Option (Fin m)) (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j ∧ q j ≤ 1)
    (i : Fin m) (a u v : ℝ) (ha : a ≤ 1/2) (hsupp : ∀ᵐ d : Gap ∂μ, (d : ℝ) ≤ a)
    (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ 1/2) :
    u*(1-realFiniteAffinity (gapMixture (n := n) μ pol (Function.update q i u))
      (gapMixture μ pol (Function.update q i v))) ≤
      32*(v-u)^2*a^2*(∑ w : Fin n → Option Bool, gapMixture μ pol (Function.update q i 0) w*coinWork pol i w) := by
  have hP := gapMixture_total (n := n) μ pol _ (update_range q hq i 0 (by norm_num))
  have hQ := gapMixture_total (n := n) μ pol _ (update_range q hq i 1 (by norm_num))
  have h := finite_mixture_distance u v _ _ hu huv hv hP.1 hQ.1 hP.2 hQ.2
  rw [sum_sqrt_distance _ _ hP.1 hQ.1 hP.2 hQ.2] at h
  simp_rw [← gapMixture_mix_update μ pol q hq i] at h
  have hb := mul_le_mul_of_nonneg_left (gap_sign_distance (n := n) μ pol q hq i a ha hsupp) (sq_nonneg (v-u))
  nlinarith only [h,hb]

end ThresholdHC.RareAboveTwo
