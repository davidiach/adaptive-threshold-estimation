import ThresholdHC.Genie.RevealFiniteness

/-! Removing the reveal loses at most the complete-depth information
residual. Root activation costs at least one, so the same residual bounds
the loss in the optimal information/work ratio. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

def revealGap (μ : Measure Gap) (Q : FourPriors) (n k : ℕ) : ℝ≥0∞ :=
  revealReward μ Q n k-prefixInformation μ Q n k

def terminalInformation (μ : Measure Gap) (Q : FourPriors) (N : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (N+1), ENNReal.ofReal (N.choose k:ℝ)*prefixInformation μ Q N k

def revealResidual (μ : Measure Gap) (Q : FourPriors) (N : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (N+1), ENNReal.ofReal (N.choose k:ℝ)*revealGap μ Q N k

theorem revealReward_eq_add_gap (μ : Measure Gap) [IsFiniteMeasure μ]
    (Q : FourPriors) (n k : ℕ) :
    revealReward μ Q n k = prefixInformation μ Q n k+revealGap μ Q n k :=
  (add_tsub_cancel_of_le (prefixInformation_le_revealReward μ Q n k)).symm

theorem revealResidual_add_terminal (μ : Measure Gap) [IsFiniteMeasure μ]
    (Q : FourPriors) (N : ℕ) :
    revealResidual μ Q N+terminalInformation μ Q N = latentDivergence μ Q := by
  rw [revealResidual,terminalInformation,←Finset.sum_add_distrib,←terminal_reveal_sum μ Q N]
  apply Finset.sum_congr rfl
  intro k _
  rw [←mul_add,add_comm (revealGap μ Q N k),←revealReward_eq_add_gap]

theorem revealResidual_eq_sub (μ : Measure Gap) [IsFiniteMeasure μ]
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) (N : ℕ) :
    revealResidual μ Q N = latentDivergence μ Q-terminalInformation μ Q N :=
  ENNReal.eq_sub_of_add_eq' hC (revealResidual_add_terminal μ Q N)

theorem genieFlowInformation_gap {N : ℕ} (μ : Measure Gap) [IsFiniteMeasure μ]
    (Q : FourPriors) (f : Flow N) :
    genieFlowInformation μ Q f = flowInformation μ Q f+eRawLayer f.stopWeight (revealGap μ Q) N := by
  rw [genieFlowInformation,flowInformation_raw,Finset.sum_range_succ,Finset.sum_range_succ]
  have hb : (∑ n ∈ Finset.range N, eRawLayer f.stopWeight (geniePrefixInformation μ Q N) n) =
      ∑ n ∈ Finset.range N, eRawLayer f.stopWeight (prefixInformation μ Q) n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [eRawLayer,geniePrefixInformation,show n ≠ N by have h := Finset.mem_range.mp hn; omega]
  rw [hb,add_assoc]
  congr 1
  unfold eRawLayer
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [geniePrefixInformation,ite_true,revealReward_eq_add_gap,mul_add]

theorem raw_stop_le_choose {N : ℕ} (f : Flow N) (hf : FlowCone f) (hi : intensity f = 1)
    (n k : ℕ) : rawArray f.stopWeight n k ≤ (n.choose k:ℝ) := by
  have hs : arrayAt f.stopWeight n k ≤ 1 := by
    apply arrayAt_le_of N n k _ (by norm_num)
    intro s _
    exact (flow_stop_le_intensity f hf s).trans_eq hi
  simpa only [rawArray,mul_one] using mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (n.choose k))

theorem genieFlowInformation_le_add_residual {N : ℕ} (μ : Measure Gap) [IsFiniteMeasure μ]
    (Q : FourPriors) (f : Flow N) (hf : FlowCone f) (hi : intensity f = 1) :
    genieFlowInformation μ Q f ≤ flowInformation μ Q f+revealResidual μ Q N := by
  rw [genieFlowInformation_gap]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (raw_stop_le_choose f hf hi N k)) _

theorem genieInformationRatio_le_add_residual (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : FourPriors) :
    genieInformationRatio μ N Q ≤ informationRatio μ N Q+revealResidual μ Q N := by
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  apply iSup_le
  intro hi
  have hw := flow_work_ge_intensity μ Q.work f hf
  rw [hi] at hw
  have hw' : (1:ℝ≥0∞) ≤ ENNReal.ofReal (countMean μ Q.work f.continueWeight) := by
    simpa using ENNReal.ofReal_le_ofReal hw
  calc
    _ ≤ (flowInformation μ Q f+revealResidual μ Q N)/
        ENNReal.ofReal (countMean μ Q.work f.continueWeight) :=
      ENNReal.div_le_div_right (genieFlowInformation_le_add_residual μ Q f hf hi) _
    _ = flowInformation μ Q f/ENNReal.ofReal (countMean μ Q.work f.continueWeight)+
        revealResidual μ Q N/ENNReal.ofReal (countMean μ Q.work f.continueWeight) := ENNReal.add_div
    _ ≤ informationRatio μ N Q+revealResidual μ Q N := add_le_add
      (le_iSup_of_le f (le_iSup_of_le hf (le_iSup_of_le hi le_rfl)))
      ((ENNReal.div_le_div_left hw' _).trans_eq (div_one _))

theorem genie_information_error (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) :
    genieInformationRatio μ N Q-informationRatio μ N Q ≤
      latentDivergence μ Q-terminalInformation μ Q N := by
  rw [←revealResidual_eq_sub μ Q hC N]
  exact tsub_le_iff_right.mpr (by
    simpa only [add_comm] using genieInformationRatio_le_add_residual μ N Q)

end ThresholdHC.Genie
