import ThresholdHC.EntropyTailAssembly.OrdinaryKernels

/-! The least power-of-four cap achieving a prescribed population error.
The lower error estimate and strict ordering use minimality, not an assumed
regularity or inverse moment of the population law. -/

noncomputable section
open MeasureTheory Set Real Filter
open scoped Topology

namespace ThresholdHC.EntropyTailAssembly
open ThresholdHC.Tier6 ThresholdHC.EntropyTailUpper

theorem ordinaryErrorKernel_tendsto (d : Gap) :
    Tendsto (fun k : ℕ => ordinaryErrorKernel (4^k) (d:ℝ)) atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 4)
  have hm := hp.atTop_mul_const (sq_pos_of_pos d.property.1)
  have hi := tendsto_inv_atTop_zero.comp hm
  simpa [ordinaryErrorKernel] using (tendsto_const_nhds (x := (1:ℝ))).min (hi.pow 2)

theorem eta_tendsto (ξ : Measure Gap) [IsFiniteMeasure ξ] :
    Tendsto (fun k : ℕ => eta ξ (4^k)) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := ξ) (fun _ => (1:ℝ))
    (F := fun (k : ℕ) (d : Gap) => ordinaryErrorKernel (4^k) (d:ℝ)) (f := fun _ => (0:ℝ))
    (fun k => by
      have hm : Measurable (fun d : Gap => ordinaryErrorKernel (4^k) (d:ℝ)) := by
        unfold ordinaryErrorKernel
        fun_prop
      exact hm.aestronglyMeasurable)
    (integrable_const 1)
    (fun k => ae_of_all _ (fun d => by
      rw [Real.norm_of_nonneg (ordinaryErrorKernel_nonneg _ _)]
      exact min_le_left _ _))
    (ae_of_all _ ordinaryErrorKernel_tendsto)
  simpa [eta] using h

theorem exists_error_cap (ξ : Measure Gap) [IsFiniteMeasure ξ]
    {δ : ℝ} (hδ : 0 < δ) : ∃ k : ℕ, 1 ≤ k ∧ eta ξ (4^k) ≤ δ/8 := by
  have he := (eta_tendsto ξ).eventually (gt_mem_nhds (by positivity : (0:ℝ) < δ/8))
  obtain ⟨k, hk, he⟩ := (eventually_ge_atTop 1 |>.and he).exists
  exact ⟨k, hk, he.le⟩

def errorCapExponent (ξ : Measure Gap) [IsFiniteMeasure ξ] (δ : ℝ) (hδ : 0 < δ) : ℕ :=
  Nat.find (exists_error_cap ξ hδ)

theorem errorCapExponent_spec (ξ : Measure Gap) [IsFiniteMeasure ξ]
    {δ : ℝ} (hδ : 0 < δ) :
    1 ≤ errorCapExponent ξ δ hδ ∧ eta ξ (4^(errorCapExponent ξ δ hδ)) ≤ δ/8 :=
  Nat.find_spec (exists_error_cap ξ hδ)

theorem errorCapExponent_min (ξ : Measure Gap) [IsFiniteMeasure ξ]
    {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : k < errorCapExponent ξ δ hδ)
    (hk1 : 1 ≤ k) : δ/8 < eta ξ (4^k) := by
  have h := Nat.find_min (exists_error_cap ξ hδ) hk
  exact lt_of_not_ge (fun he => h ⟨hk1, he⟩)

theorem errorCapExponent_gt_one (ξ : Measure Gap) [IsFiniteMeasure ξ]
    {δ : ℝ} (hδ : 0 < δ) (hm : δ/8 < ξ.real univ) :
    1 < errorCapExponent ξ δ hδ := by
  have hs := errorCapExponent_spec ξ hδ
  by_contra hn
  have he : errorCapExponent ξ δ hδ = 1 := by omega
  rw [he, pow_one, eta_four] at hs
  exact (not_le_of_gt hm) hs.2

theorem errorCapExponent_error_lower (ξ : Measure Gap) [IsFiniteMeasure ξ]
    {δ : ℝ} (hδ : 0 < δ) (hm : δ/8 < ξ.real univ) :
    δ/128 < eta ξ (4^(errorCapExponent ξ δ hδ)) := by
  let k := errorCapExponent ξ δ hδ
  have hk : 1 < k := errorCapExponent_gt_one ξ hδ hm
  have hp := errorCapExponent_min ξ hδ (k := k-1) (by omega) (by omega)
  have he := eta_four_mul ξ (4^(k-1))
  have hpow : 4 * (4:ℝ)^(k-1) = 4^k := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
  rw [hpow] at he
  change δ/128 < eta ξ (4^k)
  linarith

theorem errorCapExponent_strict (ξ : Measure Gap) [IsFiniteMeasure ξ]
    {δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (hm : δ₁/8 < ξ.real univ) (hδ : δ₂ ≤ δ₁/16) :
    errorCapExponent ξ δ₁ hδ₁ < errorCapExponent ξ δ₂ hδ₂ := by
  by_contra hn
  have hk : errorCapExponent ξ δ₂ hδ₂ ≤ errorCapExponent ξ δ₁ hδ₁ := by omega
  have hp : (4:ℝ)^(errorCapExponent ξ δ₂ hδ₂) ≤
      4^(errorCapExponent ξ δ₁ hδ₁) := by gcongr; norm_num
  have he := eta_antitone ξ (by positivity) hp
  have hl := errorCapExponent_error_lower ξ hδ₁ hm
  have hu := (errorCapExponent_spec ξ hδ₂).2
  linarith

end ThresholdHC.EntropyTailAssembly
