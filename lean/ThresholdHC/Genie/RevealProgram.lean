import ThresholdHC.Genie.RevealReward
import ThresholdHC.Genie.ExtendedFlowConservation

/-! The cap-reveal information program uses the same charged flow cone as
the ordinary experiment and substitutes only the terminal reward. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

def geniePrefixInformation (μ : Measure Gap) (Q : FourPriors) (N n k : ℕ) : ℝ≥0∞ :=
  if n = N then revealReward μ Q n k else prefixInformation μ Q n k

def genieFlowInformation {N : ℕ} (μ : Measure Gap) (Q : FourPriors) (f : Flow N) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range (N+1), eRawLayer f.stopWeight (geniePrefixInformation μ Q N) n

def genieInformationRatio (μ : Measure Gap) (N : ℕ) (Q : FourPriors) : ℝ≥0∞ :=
  ⨆ (f : Flow N) (_ : FlowCone f) (_ : intensity f = 1),
    genieFlowInformation μ Q f/ENNReal.ofReal (countMean μ Q.work f.continueWeight)

theorem prefixInformation_le_genie (μ : Measure Gap) [IsFiniteMeasure μ]
    (Q : FourPriors) (N n k : ℕ) :
    prefixInformation μ Q n k ≤ geniePrefixInformation μ Q N n k := by
  unfold geniePrefixInformation
  split_ifs
  · exact prefixInformation_le_revealReward μ Q n k
  · exact le_rfl

theorem geniePrefixInformation_le_reveal (μ : Measure Gap) [IsFiniteMeasure μ]
    (Q : FourPriors) (N n k : ℕ) :
    geniePrefixInformation μ Q N n k ≤ revealReward μ Q n k := by
  unfold geniePrefixInformation
  split_ifs
  · exact le_rfl
  · exact prefixInformation_le_revealReward μ Q n k

theorem flowInformation_le_genie {N : ℕ} (μ : Measure Gap) [IsFiniteMeasure μ]
    (Q : FourPriors) (f : Flow N) : flowInformation μ Q f ≤ genieFlowInformation μ Q f := by
  rw [flowInformation_raw]
  apply Finset.sum_le_sum
  intro n _
  exact eRawLayer_mono _ _ _ n (fun k _ => prefixInformation_le_genie μ Q N n k)

theorem informationRatio_le_genie (μ : Measure Gap) [IsFiniteMeasure μ] (N : ℕ) (Q : FourPriors) :
    informationRatio μ N Q ≤ genieInformationRatio μ N Q := by
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  apply iSup_le
  intro hi
  exact (ENNReal.div_le_div_right (flowInformation_le_genie μ Q f) _).trans
    (le_iSup_of_le f (le_iSup_of_le hf (le_iSup_of_le hi le_rfl)))

theorem eRaw_root_total {N : ℕ} (f : Flow N) (hf : FlowCone f) (v : ℕ → ℕ → ℝ≥0∞) :
    eRawLayer f.stopWeight v 0+eRawLayer f.continueWeight v 0 =
      ENNReal.ofReal (intensity f)*v 0 0 := by
  simp only [eRawLayer,zero_add,Finset.sum_range_one,rawArray,Nat.choose_zero_right,Nat.cast_one,one_mul]
  change ENNReal.ofReal (f.stopWeight (rootState N))*v 0 0+
    ENNReal.ofReal (f.continueWeight (rootState N))*v 0 0 = _
  rw [hf.root_stop,ENNReal.ofReal_zero,zero_mul,zero_add]
  rfl

theorem genieFlowInformation_le_latent {N : ℕ} (μ : Measure Gap) [IsFiniteMeasure μ]
    (Q : FourPriors) (f : Flow N) (hf : FlowCone f) :
    genieFlowInformation μ Q f ≤ ENNReal.ofReal (intensity f)*latentDivergence μ Q := by
  calc
    _ ≤ ∑ n ∈ Finset.range (N+1), eRawLayer f.stopWeight (revealReward μ Q) n := by
      apply Finset.sum_le_sum
      intro n _
      exact eRawLayer_mono _ _ _ n (fun k _ => geniePrefixInformation_le_reveal μ Q N n k)
    _ = _ := by
      have he := eRaw_tail_harmonic f hf (revealReward μ Q) (revealReward_children μ Q) 0 N (by omega)
      simp only [Nat.zero_add,eRaw_root_total f hf,revealReward_root] at he
      exact he

theorem genieInformationRatio_le_latent (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : FourPriors) : genieInformationRatio μ N Q ≤ latentDivergence μ Q := by
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
  have hinf := genieFlowInformation_le_latent μ Q f hf
  rw [hi,ENNReal.ofReal_one,one_mul] at hinf
  exact (ENNReal.div_le_div hinf hw').trans_eq (div_one _)

end ThresholdHC.Genie
