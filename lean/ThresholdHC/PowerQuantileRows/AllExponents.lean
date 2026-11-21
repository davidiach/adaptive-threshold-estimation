import ThresholdHC.PowerWindow.CoreEntropy

/-! The uniform core-entropy estimate and the deterministic quantile comparison
of `PowerWindow` for every exponent `α > 0`.

The frozen targets `PowerCoreStatement` and `PowerQuantileStatement` carry the
hypothesis `α ≤ 4` of v6 Lemma 14.12 and Theorem 14.13, but no lemma used in
their proofs needs it. The two theorems below repeat those proofs with that
hypothesis removed. This is a Lean-only extension: the paper states Theorem
14.13 for `0 < α ≤ 4` only. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.PowerQuantileRows
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile ThresholdHC.PsiGap
open ThresholdHC.PowerWindow
open ThresholdHC.RareAboveTwo (ExactPowerLaw)

/-- `PowerWindow.power_core` without the hypothesis `α ≤ 4`. -/
theorem power_core_all (μ : Measure Gap) [IsProbabilityMeasure μ] {α a ρ : ℝ}
    (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hm : ExactPowerLaw μ α a) :
    a^2 * coreCost μ ρ = powerPhi α ρ ∧
    (1/2 : ℝ) * (1 + Real.log (effectiveScales α ρ)) ≤ 1 + coreEntropy μ ρ ∧
    1 + coreEntropy μ ρ ≤ (383/100 : ℝ) * (1 + Real.log (effectiveScales α ρ)) := by
  obtain ⟨hE, hatom, hcount, hmoment⟩ := power_core_entropy_estimates μ hα ha ha2 hρ hρ1 hm
  have hM := (power_window_length hα ha hρ hρ1).1
  have hN := effective_scales_ge_one hα hρ hρ1
  have hNM : effectiveScales α ρ ≤ 1 + Real.logb 2 (1/ρ) / α := by
    rw [effective_scales_window]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hNs : 2 ≤ effectiveScales α ρ → effectiveScales α ρ * |α - 2| ≤ 1 := by
    intro h2
    by_cases hs : |α - 2| = 0
    · simp [hs]
    · have hs0 : 0 < |α - 2| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hs)
      have hn : effectiveScales α ρ ≤ max 1 (1/|α - 2|) := by
        rw [effective_scales_window, ite_eq_right hs]
        exact min_le_right _ _
      have hge : 1 ≤ 1/|α - 2| := by
        by_contra h
        rw [max_eq_left (not_le.1 h).le] at hn
        linarith
      rw [max_eq_right hge] at hn
      exact (le_div_iff₀ hs0).1 hn
  refine ⟨power_core_cost μ hα ha ha2 hρ hρ1 hm,
    entropy_window_lower hM (abs_nonneg _) hN hNM hNs hE hatom, ?_⟩
  rw [effective_scales_window]
  apply entropy_window_upper hM (abs_nonneg _) hcount
  intro hs
  exact hmoment (by intro h; simp [h] at hs)

/-- `PowerWindow.power_quantile` without the hypothesis `α ≤ 4`: the closed
quantile functional of an exact power law is the uniform rate (W7) within the
factors `1/√2` and `2`, for every exponent `α > 0`. -/
theorem power_quantile_all (μ : Measure Gap) [IsProbabilityMeasure μ] {α a ρ B : ℝ}
    (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hm : ExactPowerLaw μ α a) :
    ENNReal.ofReal (uniformRate α (1 / (a * Real.sqrt B)) ρ / Real.sqrt 2) ≤
      closedQuantileValue μ ρ B ∧
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (2 * uniformRate α (1 / (a * Real.sqrt B)) ρ) := by
  have hρ1 : ρ < 1 := by linarith
  set x := 1 / (a * Real.sqrt B) with hxdef
  have hx : 0 < x := by dsimp [x]; positivity
  have hN := effective_scales_ge_one hα hρ hρ1
  have hK : 0 ≤ 1 + Real.log (effectiveScales α ρ) := by linarith [Real.log_nonneg hN]
  obtain ⟨_, hlo, hhi⟩ := power_core_all μ hα ha ha2 hρ hρ1 hm
  have hC : 0 ≤ ρ * powerPhi α ρ := mul_nonneg hρ.le (power_phi_pos hα hρ hρ1).le
  obtain ⟨hl, hu⟩ := core_root_comparison hC hK hx.le hlo hhi
  rw [power_quantile_formula μ hα ha ha2 hρ hρ4 hB hm]
  rw [← hxdef]
  unfold uniformRate
  by_cases ht : x < powerQuantileScale α ρ
  · simp only [ite_eq_left ht]
    have hT : 0 ≤ powerTail α x ρ := by
      rw [← power_tail_formula μ hα ha ha2 hρ hρ1 hm hx ht]
      apply integral_nonneg
      intro d
      exact le_min (by norm_num) (div_nonneg (mul_nonneg ha.le hx.le) d.2.1.le)
    obtain ⟨hl', hu'⟩ := clipped_sum_comparison hρ.le hT hl hu
    exact ⟨ENNReal.ofReal_le_ofReal hl', ENNReal.ofReal_le_ofReal hu'⟩
  · simp only [ite_eq_right ht]
    exact ⟨ENNReal.ofReal_le_ofReal (div_le_self hρ.le (Real.one_le_sqrt.2 (by norm_num))),
      ENNReal.ofReal_le_ofReal (by linarith)⟩

end ThresholdHC.PowerQuantileRows
