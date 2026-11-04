import ThresholdHC.FiniteQuantile.Full

/-! At coefficient 30001 a single budget-feasible estimator works for all
rare priors. The slack in the established 28000 upper bound supplies a
witness without assuming that the minimax infimum is attained. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.FiniteQuantile
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile

theorem observable_estimator (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ∃ (S : Type) (_ : MeasurableSpace S) (A : AdaptiveEstimator S),
      RareBudget μ A ρ B ∧ rareRisk μ A ρ ≤ 30001*closedQuantileValue μ ρ B := by
  let Q := closedQuantileValue μ ρ B
  have hu : rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal 28000 * Q :=
    (EntropyTailExecution.entropy_tail_upper_28000 μ hρ hρ4 hB).trans
      (mul_le_mul' le_rfl (selectionValue_le_closedQuantileValue μ hρ (by linarith) B))
  have hn : Q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)
  have hp : 0 < rareMinimaxRisk μ ρ B :=
    (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num : (0:ℝ) < 1/16)
      (lt_min hρ (sqrt_pos.mpr (div_pos hρ hB))))).trans_le
        (StoppingProgram.bernoulli_label_minimax_floor μ ρ B hρ hρ4 hB)
  have hq : Q ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hu
    exact hp.not_ge hu
  have hqr := ENNReal.toReal_pos hq hn
  have hstrict : rareMinimaxRisk μ ρ B < ENNReal.ofReal 30001 * Q := by
    apply hu.trans_lt
    calc
      _ = ENNReal.ofReal (28000*Q.toReal) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 28000), ENNReal.ofReal_toReal hn]
      _ < ENNReal.ofReal (30001*Q.toReal) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 30001), ENNReal.ofReal_toReal hn]
  obtain ⟨x, ⟨S, inst, A, hbudget, rfl⟩, h⟩ := sInf_lt_iff.mp hstrict
  exact ⟨S, inst, A, hbudget, by simpa [Q] using h.le⟩

theorem every_estimator_lower (μ : Measure Gap) [IsProbabilityMeasure μ] (hs : μ.support.Finite)
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    {S : Type} [MeasurableSpace S] (A : AdaptiveEstimator S) (hb : RareBudget μ A ρ B) :
    ENNReal.ofReal ((10 : ℝ)⁻¹^20)*closedQuantileValue μ ρ B ≤ rareRisk μ A ρ :=
  (direct_finite_law μ hs ρ B hρ hρ4 hB).1.trans (sInf_le ⟨S, inferInstance, A, hb, rfl⟩)

end ThresholdHC.FiniteQuantile
