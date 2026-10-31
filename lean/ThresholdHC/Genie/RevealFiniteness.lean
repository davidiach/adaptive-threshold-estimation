import ThresholdHC.Genie.RevealProgram
import ThresholdHC.StoppingProgram.FullCapFlow

/-! A full-depth reveal has exactly the latent divergence. Thus a positive
cap has finite genie ratio precisely when the latent divergence is finite. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

theorem eRaw_fullCap_layer (N : ℕ) (v : ℕ → ℕ → ℝ≥0∞) (n : ℕ) (hn : n ≤ N) :
    eRawLayer (fullCapFlow N).stopWeight v n =
      if n = N then ∑ k ∈ Finset.range (N+1), ENNReal.ofReal (N.choose k:ℝ)*v N k else 0 := by
  by_cases he : n = N
  · subst n
    rw [ite_eq_left rfl]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ N := by have h := Finset.mem_range.mp hk; omega
    simp [rawArray,arrayAt,fullCapFlow,hkn]
  · rw [ite_eq_right he]
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k ≤ n := by have h := Finset.mem_range.mp hk; omega
    simp [rawArray,arrayAt,fullCapFlow,hn,hkn,he]

theorem eRaw_fullCap_reward (N : ℕ) (v : ℕ → ℕ → ℝ≥0∞) :
    (∑ n ∈ Finset.range (N+1), eRawLayer (fullCapFlow N).stopWeight v n) =
      ∑ k ∈ Finset.range (N+1), ENNReal.ofReal (N.choose k:ℝ)*v N k := by
  rw [Finset.sum_range_succ,eRaw_fullCap_layer N v N le_rfl,ite_eq_left rfl]
  have hz : (∑ n ∈ Finset.range N, eRawLayer (fullCapFlow N).stopWeight v n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hlt := Finset.mem_range.mp hn
    rw [eRaw_fullCap_layer N v n hlt.le,ite_eq_right (by omega)]
  rw [hz,zero_add]

theorem terminal_reveal_sum (μ : Measure Gap) (Q : FourPriors) (N : ℕ) :
    (∑ k ∈ Finset.range (N+1), ENNReal.ofReal (N.choose k:ℝ)*revealReward μ Q N k) =
      latentDivergence μ Q := by
  by_cases hN : N = 0
  · subst N
    simp [revealReward_root]
  · have hpos : 0 < N := by omega
    have hf := fullCapFlow_cone hpos
    have he := eRaw_tail_harmonic (fullCapFlow N) hf (revealReward μ Q)
      (revealReward_children μ Q) 0 N (by omega)
    simp only [Nat.zero_add,eRaw_root_total _ hf,fullCapFlow_intensity hpos,
      ENNReal.ofReal_one,one_mul,revealReward_root] at he
    rwa [eRaw_fullCap_reward] at he

theorem genieFlowInformation_fullCap (μ : Measure Gap) (Q : FourPriors) (N : ℕ) :
    genieFlowInformation μ Q (fullCapFlow N) = latentDivergence μ Q := by
  rw [genieFlowInformation,eRaw_fullCap_reward]
  simp only [geniePrefixInformation,ite_true]
  exact terminal_reveal_sum μ Q N

theorem genieInformationRatio_top_iff (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 0 < N) (Q : FourPriors) :
    genieInformationRatio μ N Q = ⊤ ↔ latentDivergence μ Q = ⊤ := by
  constructor
  · intro h
    exact top_le_iff.mp (h ▸ genieInformationRatio_le_latent μ N Q)
  · intro h
    apply top_le_iff.mp
    have he : genieFlowInformation μ Q (fullCapFlow N)/
        ENNReal.ofReal (countMean μ Q.work (fullCapFlow N).continueWeight) = ⊤ := by
      rw [genieFlowInformation_fullCap,h]
      exact ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top
    rw [←he]
    exact le_iSup_of_le (fullCapFlow N) (le_iSup_of_le (fullCapFlow_cone hN)
      (le_iSup_of_le (fullCapFlow_intensity hN) le_rfl))

theorem geniePrefixInformation_finite (μ : Measure Gap) [IsFiniteMeasure μ]
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) (N n k : ℕ) :
    geniePrefixInformation μ Q N n k ≠ ⊤ :=
  ne_top_of_le_ne_top hC ((geniePrefixInformation_le_reveal μ Q N n k).trans
    (revealReward_le_latentDivergence μ Q n k))

theorem genieFlowInformation_finite {N : ℕ} (μ : Measure Gap) [IsFiniteMeasure μ]
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) (f : Flow N) (hf : FlowCone f) :
    genieFlowInformation μ Q f ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC)
    (genieFlowInformation_le_latent μ Q f hf)

end ThresholdHC.Genie
