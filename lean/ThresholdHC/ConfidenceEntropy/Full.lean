import ThresholdHC.ConfidenceEntropy.Program
import ThresholdHC.ConfidenceProgram.Upper

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ConfidenceEntropy
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.Genie
open ThresholdHC.EntropyTailQuantile ThresholdHC.ConfidenceTransfer ThresholdHC.ConfidenceProgram

theorem closed_quantile_confidence_lower (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1/4) :
    ENNReal.ofReal ((10 : ℝ)⁻¹^17)*closedQuantileValue μ ρ (B/Real.log (1/δ)) ≤
      rareConfidenceRadius μ ρ B δ := by
  have hβ := div_pos hB (ThresholdHC.Confidence.confidence_log_pos hδ hδ4)
  have hp := closed_quantile_program μ hρ hρ4 hβ
  apply le_trans ?_ (stopping_confidence_lower μ hρ (by linarith) hB hδ hδ4)
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num : (30 : ℝ≥0∞) ≠ 0))
    (Or.inl (by norm_num : (30 : ℝ≥0∞) ≠ ∞))).mpr
  calc
    _ = ENNReal.ofReal (30*(10 : ℝ)⁻¹^17)*closedQuantileValue μ ρ (B/Real.log (1/δ)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 30),ENNReal.ofReal_ofNat]
      rw [mul_assoc,mul_comm (closedQuantileValue μ ρ (B/Real.log (1/δ))) (30 : ℝ≥0∞),
        ← mul_assoc,mul_comm (ENNReal.ofReal ((10 : ℝ)⁻¹^17)) (30 : ℝ≥0∞)]
    _ ≤ _ := hp

theorem entropy_tail_confidence_lower_explicit (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1/4) :
    ENNReal.ofReal ((10 : ℝ)⁻¹^17)*EntropyTail.selection μ ρ (B/Real.log (1/δ)) ≤
      rareConfidenceRadius μ ρ B δ :=
  (mul_le_mul' le_rfl (EntropyTail.selection_quantile_comparison μ hρ hρ4
    (div_pos hB (ThresholdHC.Confidence.confidence_log_pos hδ hδ4))).1).trans
      (closed_quantile_confidence_lower μ hρ hρ4 hB hδ hδ4)

theorem estimator_confidence_lower_explicit {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    {ρ B δ ε : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1/4) (hε : 0 ≤ ε)
    (hw : RareBudget μ A ρ B)
    (hc : ∀ q : SignLaw, RarePrior μ ρ q →
      ThresholdHC.Confidence.failureProbability μ A q ε ≤ ENNReal.ofReal δ) :
    ENNReal.ofReal ((10 : ℝ)⁻¹^17)*EntropyTail.selection μ ρ (B/Real.log (1/δ)) ≤ ENNReal.ofReal ε :=
  (entropy_tail_confidence_lower_explicit μ hρ hρ4 hB hδ hδ4).trans
    (sInf_le ⟨R,inferInstance,A,ε,hε,hw,hc,rfl⟩)

/-- The sharper lower coefficient and the existing hard-cap upper coefficient
hold for every known positive-gap law in the original observable experiment. -/
theorem general_confidence_law_explicit (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1/4) :
    let K := EntropyTail.selection μ ρ (B/Real.log (1/δ))
    ENNReal.ofReal ((10 : ℝ)⁻¹^17)*K ≤ rareConfidenceRadius μ ρ B δ ∧
      rareConfidenceRadius μ ρ B δ ≤ hardConfidenceRadius μ ρ B δ ∧
      hardConfidenceRadius μ ρ B δ ≤ 750000*K :=
  ⟨entropy_tail_confidence_lower_explicit μ hρ hρ4 hB hδ hδ4,
    expected_confidence_le_hard μ hB.le,general_hard_confidence_upper μ hρ hρ4 hB hδ hδ4⟩

end ThresholdHC.ConfidenceEntropy
