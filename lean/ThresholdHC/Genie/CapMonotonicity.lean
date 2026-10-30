import ThresholdHC.Genie.FlowExtension

/-! Increasing the cap enlarges the feasible stopping class: information
ratios increase and the robust primal certificate values decrease. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 (Gap SignLaw)
open ThresholdHC.StoppingProgram

theorem flowInformation_extendFlow {N M : ℕ} (hNM : N ≤ M) (μ : Measure Gap)
    (Q : FourPriors) (f : Flow N) : flowInformation μ Q (extendFlow M f) = flowInformation μ Q f := by
  rw [flowInformation_raw,flowInformation_raw]
  simp only [extendFlow,rawArray,arrayAt_extendArray hNM]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro n hn hnN
  have hn' : ¬n ≤ N := by simp only [Finset.mem_range] at hnN; omega
  simp [arrayAt,hn']

theorem informationRatio_mono (μ : Measure Gap) (Q : FourPriors) :
    Monotone (fun N => informationRatio μ N Q) := by
  intro N M hNM
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  apply iSup_le
  intro hi
  have h : flowInformation μ Q (extendFlow M f)/
      ENNReal.ofReal (countMean μ Q.work (extendFlow M f).continueWeight) ≤ informationRatio μ M Q :=
    le_iSup_of_le (extendFlow M f) (le_iSup_of_le (extendFlow_cone hNM f hf)
      (le_iSup_of_le (by simpa only [extendFlow_intensity] using hi) le_rfl))
  rw [flowInformation_extendFlow hNM] at h
  change flowInformation μ Q f/ENNReal.ofReal (countMean μ Q.work (extendArray M f.continueWeight)) ≤ _ at h
  rwa [countMean_extendArray hNM] at h

def extendCertificate {N : ℕ} (M : ℕ) (C : Certificate N) : Certificate M :=
  ⟨extendFlow M C.flow,C.offset,C.bias,C.variance⟩

theorem feasible_extendCertificate {N M : ℕ} (hNM : N ≤ M) (μ : Measure Gap)
    (ρ B : ℝ) (C : Certificate N) (hC : Feasible μ ρ B C) :
    Feasible μ ρ B (extendCertificate M C) := by
  constructor
  · exact extendFlow_cone hNM C.flow hC.cone
  · exact hC.bias_nonneg
  · exact hC.variance_nonneg
  · intro q hq
    change |C.offset+countMean μ q (extendArray M C.flow.outputWeight)-ThresholdHC.Tier6.signMean μ q.val| ≤ C.bias
    rw [countMean_extendArray hNM]
    exact hC.bias_bound q hq
  · intro q hq
    change countMean μ q (extendArray M C.flow.momentWeight) ≤ C.variance
    rw [countMean_extendArray hNM]
    exact hC.variance_bound q hq
  · intro q hq
    change countMean μ q (extendArray M C.flow.continueWeight) ≤ B
    rw [countMean_extendArray hNM]
    exact hC.work_bound q hq

theorem programSquared_antitone (μ : Measure Gap) (ρ B : ℝ) :
    Antitone (fun N => programSquared μ ρ B N) := by
  intro N M hNM
  apply le_sInf
  rintro x ⟨C,hC,rfl⟩
  exact sInf_le ⟨extendCertificate M C,feasible_extendCertificate hNM μ ρ B C hC,rfl⟩

theorem programValue_antitone (μ : Measure Gap) (ρ B : ℝ) :
    Antitone (fun N => programValue μ ρ B N) := by
  intro N M hNM
  exact ENNReal.rpow_le_rpow (programSquared_antitone μ ρ B hNM) (by norm_num)

end ThresholdHC.Genie
