import ThresholdHC.EntropyTailExecution.FiniteRisk
import ThresholdHC.EntropyTailAssembly.FiniteApproximation

/-! Terminal-level selection, including zero unresolved mass. The zero-mass
case passes to the infimum of finite estimators, not an infinite execution. -/

noncomputable section
open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace ThresholdHC.EntropyTailExecution
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailAssembly ThresholdHC.RareAboveTwo

theorem minimax_half_rarity (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ} (hρ : 0 ≤ ρ) :
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (ρ/2) := by
  have h : rareMinimaxRisk μ ρ B ≤ rareRisk μ (constantEstimator (ρ/2)) ρ :=
    sInf_le ⟨Unit, inferInstance, constantEstimator (ρ/2), constant_rare_budget μ ρ B (ρ/2), rfl⟩
  exact h.trans (half_rarity_risk μ ρ hρ)

theorem resolved_mass_large (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {ρ : ℝ} (hρ1 : ρ ≤ 1/4) (hz : ζ.real univ ≤ ρ/128) : ρ/128 < (σ+τ).real univ := by
  have he : (σ+τ).real univ+ζ.real univ = 1 := by
    rw [← measureReal_add_apply]
    exact probReal_univ
  linarith

theorem finite_support_three_piece (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 < B) :
    rareMinimaxRisk (σ+τ+ζ) ρ B ≤ ENNReal.ofReal (128*ζ.real univ+
      28000*(sqrt (ρ*costEntropy (fun j : Fin N => bandCost σ j.val))+
        (∫ d : Gap, (d:ℝ)⁻¹ ∂τ))/sqrt B) := by
  let X := 28000*(sqrt (ρ*costEntropy (fun j : Fin N => bandCost σ j.val))+
    (∫ d : Gap, (d:ℝ)⁻¹ ∂τ))/sqrt B
  have hX : 0 ≤ X := by
    have hH : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂τ := integral_nonneg (fun d => inv_nonneg.mpr d.property.1.le)
    dsimp only [X]
    positivity
  change rareMinimaxRisk (σ+τ+ζ) ρ B ≤ ENNReal.ofReal (128*ζ.real univ+X)
  by_cases hz : ζ.real univ ≤ ρ/128
  · have hm := resolved_mass_large σ τ ζ hρ1 hz
    by_cases hz0 : ζ.real univ = 0
    · have hl : Tendsto (fun J => ENNReal.ofReal (levelAccuracy ρ J+X)) atTop
          (𝓝 (ENNReal.ofReal X)) := by
        simpa only [zero_add] using ENNReal.tendsto_ofReal ((levelAccuracy_tendsto ρ).add_const X)
      rw [hz0, mul_zero, zero_add]
      exact ge_of_tendsto hl (Eventually.of_forall (fun J =>
        finite_level_minimax σ τ ζ ht hs hN hτ hρ hρ1 hB hm J
          (by rw [hz0]; positivity [levelAccuracy_pos hρ J])))
    · obtain ⟨J,hl,hu⟩ := exists_terminal_level hρ (lt_of_le_of_ne measureReal_nonneg (Ne.symm hz0)) hz
      exact (finite_level_minimax σ τ ζ ht hs hN hτ hρ hρ1 hB hm J (by linarith)).trans
        (ENNReal.ofReal_le_ofReal (add_le_add hu.le (le_refl X)))
  · exact (minimax_half_rarity (σ+τ+ζ) hρ.le).trans
      (ENNReal.ofReal_le_ofReal (by have h := lt_of_not_ge hz; linarith))

end ThresholdHC.EntropyTailExecution
