import ThresholdHC.StoppingProgram.PrefixInformation

/-! Prefix information is a nonnegative incremental reward, and its sum
against continuation flow equals the terminal stopping information. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap)

def informationIncrement (μ : Measure Gap) (Q : FourPriors) (n k : ℕ) : ℝ :=
  prefixReward μ Q (n+1) k+prefixReward μ Q (n+1) (k+1)-prefixReward μ Q n k

theorem informationIncrement_nonneg (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (n k : ℕ) (hk : k ≤ n)
    (h0 : prefixInformation μ Q (n+1) k ≠ ⊤)
    (h1 : prefixInformation μ Q (n+1) (k+1) ≠ ⊤) : 0 ≤ informationIncrement μ Q n k := by
  have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h0,h1⟩) (prefixInformation_children μ Q n k hk)
  rw [ENNReal.toReal_add h0 h1] at hh
  exact sub_nonneg.mpr hh

theorem flowInformation_increments {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (f : Flow N) (hf : FlowCone f)
    (hfin : ∀ n k, n ≤ N → k ≤ n → prefixInformation μ Q n k ≠ ⊤) :
    (flowInformation μ Q f).toReal = ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (n+1),
      rawArray f.continueWeight n k*informationIncrement μ Q n k := by
  have ht := raw_weighted_telescope f hf (prefixReward μ Q)
  have hz : prefixReward μ Q 0 0 = 0 := by rw [prefixReward,prefixInformation_root,ENNReal.toReal_zero]
  rw [hz,mul_zero] at ht
  rw [flowInformation_toReal_raw μ Q f hf hfin]
  have he : (∑ n ∈ Finset.range (N+1), rawLayer f.stopWeight (prefixReward μ Q) n) =
      ∑ n ∈ Finset.range (N+1), ∑ k ∈ Finset.range (n+1),
        rawArray f.continueWeight n k*informationIncrement μ Q n k := by
    have hsub : (∑ n ∈ Finset.range (N+1), rawLayer f.stopWeight (prefixReward μ Q) n)-
        (∑ n ∈ Finset.range (N+1), ∑ k ∈ Finset.range (n+1),
          rawArray f.continueWeight n k*informationIncrement μ Q n k) = 0 := by
      rw [← ht,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _
      unfold rawLayer rawChildren informationIncrement
      rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    exact sub_eq_zero.mp hsub
  rw [he,Finset.sum_range_succ]
  simp only [rawArray_terminal f hf,zero_mul,Finset.sum_const_zero,add_zero]

end ThresholdHC.StoppingProgram
