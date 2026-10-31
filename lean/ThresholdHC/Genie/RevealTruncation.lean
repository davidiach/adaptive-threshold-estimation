import ThresholdHC.Genie.RevealProgram
import ThresholdHC.Genie.FlowTruncation
import ThresholdHC.Genie.CapMonotonicity

/-! Truncating paid observations and revealing the latent state dominates
every later capped policy. No finite-divergence assumption is used. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

theorem genieFlowInformation_truncate {M : ℕ} (N : ℕ) (μ : Measure Gap)
    (Q : FourPriors) (f : Flow M) (hf : FlowCone f) :
    genieFlowInformation μ Q (truncateFlow N f) =
      (∑ n ∈ Finset.range N, eRawLayer f.stopWeight (prefixInformation μ Q) n)+
        (eRawLayer f.stopWeight (revealReward μ Q) N+eRawLayer f.continueWeight (revealReward μ Q) N) := by
  rw [genieFlowInformation,Finset.sum_range_succ]
  have hb : (∑ n ∈ Finset.range N, eRawLayer (truncateFlow N f).stopWeight (geniePrefixInformation μ Q N) n) =
      ∑ n ∈ Finset.range N, eRawLayer f.stopWeight (prefixInformation μ Q) n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hlt := Finset.mem_range.mp hn
    rw [eRaw_truncate_stop_before N f _ n hlt]
    simp [eRawLayer,geniePrefixInformation,show n ≠ N by omega]
  rw [hb]
  have ht : eRawLayer (truncateFlow N f).stopWeight (geniePrefixInformation μ Q N) N =
      eRawLayer (truncateFlow N f).stopWeight (revealReward μ Q) N := by
    simp [eRawLayer,geniePrefixInformation]
  rw [ht,eRaw_truncate_stop_terminal N f hf]

theorem capped_reward_le_truncated_reveal {M N : ℕ} (hNM : N ≤ M) (μ : Measure Gap)
    (Q : FourPriors) (f : Flow M) (hf : FlowCone f) (r : ℕ → ℕ → ℝ≥0∞)
    (hbefore : ∀ n k, n < N → k ≤ n → r n k = prefixInformation μ Q n k)
    (hbound : ∀ n k, k ≤ n → r n k ≤ revealReward μ Q n k) :
    (∑ n ∈ Finset.range (M+1), eRawLayer f.stopWeight r n) ≤
      genieFlowInformation μ Q (truncateFlow N f) := by
  rw [genieFlowInformation_truncate N μ Q f hf,
    show M+1 = N+(M-N+1) by omega,Finset.sum_range_add]
  apply add_le_add
  · apply le_of_eq
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro k hk
    rw [hbefore n k (Finset.mem_range.mp hn) (by have h := Finset.mem_range.mp hk; omega)]
  · calc
      _ ≤ ∑ i ∈ Finset.range (M-N+1), eRawLayer f.stopWeight (revealReward μ Q) (N+i) := by
        apply Finset.sum_le_sum
        intro i _
        exact eRawLayer_mono _ _ _ (N+i) (hbound (N+i))
      _ = _ := eRaw_tail_harmonic f hf _ (revealReward_children μ Q) N (M-N) (by omega)

theorem flowInformation_le_truncated_reveal {M N : ℕ} (hNM : N ≤ M)
    (μ : Measure Gap) [IsFiniteMeasure μ] (Q : FourPriors) (f : Flow M) (hf : FlowCone f) :
    flowInformation μ Q f ≤ genieFlowInformation μ Q (truncateFlow N f) := by
  rw [flowInformation_raw]
  exact capped_reward_le_truncated_reveal hNM μ Q f hf (prefixInformation μ Q)
    (fun _ _ _ _ => rfl) (fun n k _ => prefixInformation_le_revealReward μ Q n k)

theorem genieFlowInformation_le_truncated {M N : ℕ} (hNM : N ≤ M)
    (μ : Measure Gap) [IsFiniteMeasure μ] (Q : FourPriors) (f : Flow M) (hf : FlowCone f) :
    genieFlowInformation μ Q f ≤ genieFlowInformation μ Q (truncateFlow N f) := by
  apply capped_reward_le_truncated_reveal hNM μ Q f hf (geniePrefixInformation μ Q M)
  · intro n k hn _
    simp [geniePrefixInformation,show n ≠ M by omega]
  · intro n k _
    exact geniePrefixInformation_le_reveal μ Q M n k

theorem informationRatio_le_earlier_genie {M N : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    (μ : Measure Gap) [IsFiniteMeasure μ] (Q : FourPriors) :
    informationRatio μ M Q ≤ genieInformationRatio μ N Q := by
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  apply iSup_le
  intro hi
  have hft := truncateFlow_cone hN hNM f hf
  have hit : intensity (truncateFlow N f) = 1 := (truncateFlow_intensity N hN f).trans hi
  exact (ENNReal.div_le_div (flowInformation_le_truncated_reveal hNM μ Q f hf)
    (ENNReal.ofReal_le_ofReal (truncateFlow_work_le hNM μ Q.work f hf))).trans
      (le_iSup_of_le (truncateFlow N f) (le_iSup_of_le hft (le_iSup_of_le hit le_rfl)))

theorem genieInformationRatio_antitone_cap {M N : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    (μ : Measure Gap) [IsFiniteMeasure μ] (Q : FourPriors) :
    genieInformationRatio μ M Q ≤ genieInformationRatio μ N Q := by
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  apply iSup_le
  intro hi
  have hft := truncateFlow_cone hN hNM f hf
  have hit : intensity (truncateFlow N f) = 1 := (truncateFlow_intensity N hN f).trans hi
  exact (ENNReal.div_le_div (genieFlowInformation_le_truncated hNM μ Q f hf)
    (ENNReal.ofReal_le_ofReal (truncateFlow_work_le hNM μ Q.work f hf))).trans
      (le_iSup_of_le (truncateFlow N f) (le_iSup_of_le hft (le_iSup_of_le hit le_rfl)))

theorem infiniteInformationRatio_le_genie (μ : Measure Gap) [IsFiniteMeasure μ]
    (N : ℕ) (hN : 0 < N) (Q : FourPriors) :
    infiniteInformationRatio μ Q ≤ genieInformationRatio μ N Q := by
  apply iSup_le
  intro M
  by_cases hNM : N ≤ M+1
  · exact informationRatio_le_earlier_genie hN hNM μ Q
  · exact (informationRatio_mono μ Q (show M+1 ≤ N by omega)).trans (informationRatio_le_genie μ N Q)

theorem genieInformationRatio_antitone (μ : Measure Gap) [IsFiniteMeasure μ] (Q : FourPriors) :
    Antitone (fun N : ℕ => genieInformationRatio μ (N+1) Q) := by
  intro N M hNM
  exact genieInformationRatio_antitone_cap (by omega) (by omega) μ Q

end ThresholdHC.Genie
