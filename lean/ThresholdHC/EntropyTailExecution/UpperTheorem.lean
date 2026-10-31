import ThresholdHC.EntropyTailExecution.EntropyLimit
import ThresholdHC.EntropyTailQuantile.QuantileComparison

/-! The arbitrary-law entropy-tail upper theorem in the frozen observable
experiment, and its closed-quantile upper corollary. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal

namespace ThresholdHC.EntropyTailExecution
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailAssembly ThresholdHC.RareAboveTwo

theorem minimax_le_selectionCost (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 < B)
    (σ : Measure Gap) (hσ : σ ≤ μ) :
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal 28000*selectionCost μ σ ρ (budgetScale B) := by
  have hh := budgetScale_pos hB
  let : IsFiniteMeasure σ := isFiniteMeasure_of_le μ hσ
  by_cases hG : measureCostEntropy σ = ⊤
  · have he : selectionCost μ σ ρ (budgetScale B) = ⊤ := by
      simp [selectionCost, hG, ENNReal.mul_top, ENNReal.ofReal_eq_zero, not_le.mpr hρ, not_le.mpr hh]
    rw [he]
    simp
  let ν := μ-σ
  let τ := ν.restrict {d : Gap | budgetScale B ≤ (d:ℝ)}
  let ζ := ν.restrict {d : Gap | (d:ℝ) < budgetScale B}
  have hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ) :=
    ae_restrict_mem (measurableSet_le measurable_const measurable_subtype_coe)
  have hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B := by
    filter_upwards [ae_restrict_mem (measurableSet_lt measurable_subtype_coe
      (measurable_const (a := budgetScale B)))] with d hd
    exact hd.le
  have hsplit : τ+ζ = ν := by
    have he : {d : Gap | (d:ℝ) < budgetScale B} = {d : Gap | budgetScale B ≤ (d:ℝ)}ᶜ := by
      ext d; simp
    dsimp only [τ,ζ]
    rw [he]
    exact Measure.restrict_add_restrict_compl (measurableSet_le measurable_const measurable_subtype_coe)
  have hpop : σ+τ+ζ = μ := by
    rw [add_assoc, hsplit, add_comm]
    exact Measure.sub_add_cancel_of_le hσ
  let : IsProbabilityMeasure (σ+τ+ζ) := by rw [hpop]; infer_instance
  have htail : tailModulus ν (budgetScale B) =
      budgetScale B*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)+ζ.real univ := by
    rw [← hsplit, tailModulus_add τ ζ hh.le, tailModulus_eq_inverseCost τ hτs, tailModulus_eq_mass ζ hζs]
  have h := finite_entropy_three_piece σ τ ζ (lt_top_iff_ne_top.mpr hG)
    (inverse_integrable_of_support τ hh hτs) hρ hρ1 hB
  simp only [hpop] at h
  have hreal : 128*ζ.real univ+
      28000*(sqrt (ρ*(measureCostEntropy σ).toReal)+(∫ d : Gap, (d:ℝ)⁻¹ ∂τ))/sqrt B ≤
      28000*(budgetScale B*sqrt (ρ*(measureCostEntropy σ).toReal)+tailModulus ν (budgetScale B)) := by
    rw [htail]
    unfold budgetScale
    simp only [div_eq_mul_inv]
    have hz : 0 ≤ ζ.real univ := measureReal_nonneg
    nlinarith only [hz]
  apply (h.trans (ENNReal.ofReal_le_ofReal hreal)).trans_eq
  rw [selectionCost, entropy_root_eq_ofReal hG hρ.le hh.le,
    ← ENNReal.ofReal_add (mul_nonneg hh.le (sqrt_nonneg _)) (tailModulus_nonneg _ hh.le),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 28000)]

theorem entropy_tail_upper_28000 (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 < B) :
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal 28000*selectionValue μ ρ B := by
  unfold selectionValue
  rw [mul_min]
  apply le_min
  · apply (minimax_half_rarity μ hρ.le).trans
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 28000)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [ENNReal.mul_iInf_of_ne (by norm_num : ENNReal.ofReal 28000 ≠ 0) ENNReal.ofReal_ne_top]
    apply le_iInf
    intro σ
    rw [ENNReal.mul_iInf_of_ne (by norm_num : ENNReal.ofReal 28000 ≠ 0) ENNReal.ofReal_ne_top]
    apply le_iInf
    exact minimax_le_selectionCost μ hρ hρ1 hB σ

theorem entropy_tail_upper : EntropyTailUpperStatement := by
  intro μ _ ρ B hρ hρ1 hB
  exact (entropy_tail_upper_28000 μ hρ hρ1 hB).trans
    (mul_le_mul_left (by norm_num : ENNReal.ofReal 28000 ≤ ENNReal.ofReal 33000) _)

theorem closed_quantile_upper : ClosedQuantileUpperStatement := by
  intro μ _ ρ B hρ hρ1 hB
  exact (entropy_tail_upper μ ρ B hρ hρ1 hB).trans
    (mul_le_mul_right (selectionValue_le_closedQuantileValue μ hρ (by linarith) B) _)

/-- This also gives the finite-law paper's separate upper coefficient, for
every probability law; no statistical entropy-tail lower theorem is used. -/
theorem closed_quantile_upper_30001 (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 < B) :
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal 30001*closedQuantileValue μ ρ B := by
  exact ((entropy_tail_upper_28000 μ hρ hρ1 hB).trans
    (mul_le_mul_right (selectionValue_le_closedQuantileValue μ hρ (by linarith) B) _)).trans
      (mul_le_mul_left (by norm_num : ENNReal.ofReal 28000 ≤ ENNReal.ofReal 30001) _)

end ThresholdHC.EntropyTailExecution
