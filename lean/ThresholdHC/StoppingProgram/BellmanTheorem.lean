import ThresholdHC.StoppingProgram.InformationFiniteness
import ThresholdHC.StoppingProgram.InformationIncrement

/-! Full finite-cap Bellman characterization of the actual count-flow
information ratio, with explicit deterministic attainment and null states. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap)

theorem informationRatio_bellman (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : FourPriors) (hN : 0 < N) (hK : informationRatio μ N Q ≠ ⊤) :
    informationRatio μ N Q = ENNReal.ofReal (bellmanRatio μ N Q) ∧
    (∀ κ : ℝ, rootBellman (prefixReward μ Q) (prefixCoefficient μ Q.work) κ (N-1) = 0 ↔
      κ = (informationRatio μ N Q).toReal) ∧
    ∃ p : ℕ → ℕ → ℝ, (∀ n k, p n k = 0 ∨ p n k = 1) ∧ p 0 0 = 0 ∧
      (∀ k, k ≤ N → p N k = 1) ∧ FlowCone (policyFlow N p) ∧ intensity (policyFlow N p) = 1 ∧
      flowInformation μ Q (policyFlow N p)/
        ENNReal.ofReal (countMean μ Q.work (policyFlow N p).continueWeight) = informationRatio μ N Q := by
  have hfin := prefixInformation_finite_of_ratio μ Q hN hK
  obtain ⟨he,hcone,hi,hr⟩ := informationRatio_bellman_attained μ N Q hN hfin
  refine ⟨he,fun κ => informationRatio_bellman_zero μ N Q hN hfin κ,
    bellmanStopProbability (prefixReward μ Q) (prefixCoefficient μ Q.work) (bellmanRatio μ N Q) N,
    ?_,?_,?_,hcone,hi,hr⟩
  · exact bellmanStopProbability_binary _ _ _ N
  · exact bellmanStopProbability_root _ _ _ N
  · intro k _
    exact bellmanStopProbability_terminal _ _ _ hN k

theorem informationRatio_increment_identity (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : FourPriors) (hN : 0 < N) (hK : informationRatio μ N Q ≠ ⊤)
    (f : Flow N) (hf : FlowCone f) :
    (∀ n k, n < N → k ≤ n → 0 ≤ informationIncrement μ Q n k) ∧
    (flowInformation μ Q f).toReal = ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (n+1),
      rawArray f.continueWeight n k*informationIncrement μ Q n k := by
  have hfin := prefixInformation_finite_of_ratio μ Q hN hK
  refine ⟨?_,flowInformation_increments μ Q f hf hfin⟩
  intro n k hn hk
  exact informationIncrement_nonneg μ Q n k hk
    (hfin _ _ (by omega) (by omega)) (hfin _ _ (by omega) (by omega))

end ThresholdHC.StoppingProgram
