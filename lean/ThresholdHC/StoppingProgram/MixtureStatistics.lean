import ThresholdHC.StoppingProgram.FlowTableRates

/-! Actual population moments of the finite table mixture equal the
certificate flow's count means. Null-rate tables contribute zero. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw)
open ThresholdHC.ObservableSimulation

theorem flow_mixture_mean {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (f : Flow N) (hf : FlowCone f) (hN : 0 < N) (y : CountState N → ℝ) :
    (∑ b : CountState N → Bool, flowTableRate f b*(∫ ω, tableValue b y ω ∂originalPopulationTapeLaw μ q)) =
      countMean μ q (fun s => f.stopWeight s*y s) := by
  have he (b : CountState N → Bool) :
      flowTableRate f b*(∫ ω, tableValue b y ω ∂originalPopulationTapeLaw μ q) =
      flowTableRate f b*(∑ n ∈ Finset.range (N+1), ∑ k ∈ Finset.range (n+1),
        policyArrival 1 (countDecision b) n k*countDecision b n k*prefixCoefficient μ q n k*arrayAt y n k) := by
    by_cases hr : flowTableRate f b = 0
    · simp only [hr,zero_mul]
    · obtain ⟨hb,ht⟩ := flowTableRate_supported f hf hN b hr
      rw [tableValue_integral μ q hN b hb ht]
  rw [Finset.sum_congr rfl (fun b _ => he b),← rawLayer_countMean μ q (fun s => f.stopWeight s*y s)]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  unfold rawLayer
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hnN : n ≤ N := by have h := Finset.mem_range.mp hn; omega
  have hkn : k ≤ n := by have h := Finset.mem_range.mp hk; omega
  let s : CountState N := ⟨⟨n,by omega⟩,⟨k,by change k < n+1; omega⟩⟩
  have hs := flowTableRate_stop f hf s
  change (∑ b : CountState N → Bool, flowTableRate f b*(policyArrival 1 (countDecision b) n k*countDecision b n k)) =
    rawArray f.stopWeight n k at hs
  rw [rawArray_mul]
  calc
    _ = (∑ b : CountState N → Bool, flowTableRate f b*(policyArrival 1 (countDecision b) n k*countDecision b n k))*
        prefixCoefficient μ q n k*arrayAt y n k := by
      rw [Finset.sum_mul,Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ = _ := by rw [hs]; ring

theorem flow_mixture_second_moment {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (f : Flow N) (hf : FlowCone f) (hN : 0 < N) (y : CountState N → ℝ) :
    (∑ b : CountState N → Bool, flowTableRate f b*(∫ ω, (tableValue b y ω)^2 ∂originalPopulationTapeLaw μ q)) =
      countMean μ q (fun s => f.stopWeight s*(y s)^2) := by
  simp only [tableValue_sq]
  exact flow_mixture_mean μ q f hf hN (fun s => (y s)^2)

theorem flow_mixture_work {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (f : Flow N) (hf : FlowCone f) (hN : 0 < N) :
    (∑ b : CountState N → Bool, flowTableRate f b*(∫ ω, (tableCost b ω:ℝ) ∂originalPopulationTapeLaw μ q)) =
      countMean μ q f.continueWeight := by
  have he (b : CountState N → Bool) :
      flowTableRate f b*(∫ ω, (tableCost b ω:ℝ) ∂originalPopulationTapeLaw μ q) =
      flowTableRate f b*(∑ n ∈ Finset.range (N+1), ∑ k ∈ Finset.range (n+1),
        policyArrival 1 (countDecision b) n k*(1-countDecision b n k)*prefixCoefficient μ q n k) := by
    by_cases hr : flowTableRate f b = 0
    · simp only [hr,zero_mul]
    · obtain ⟨hb,ht⟩ := flowTableRate_supported f hf hN b hr
      rw [tableCost_integral μ q hN b hb ht]
  rw [Finset.sum_congr rfl (fun b _ => he b),← rawLayer_countMean μ q f.continueWeight]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  unfold rawLayer
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hnN : n ≤ N := by have h := Finset.mem_range.mp hn; omega
  have hkn : k ≤ n := by have h := Finset.mem_range.mp hk; omega
  let s : CountState N := ⟨⟨n,by omega⟩,⟨k,by change k < n+1; omega⟩⟩
  have hs := flowTableRate_continue f hf s
  change (∑ b : CountState N → Bool, flowTableRate f b*(policyArrival 1 (countDecision b) n k*(1-countDecision b n k))) =
    rawArray f.continueWeight n k at hs
  calc
    _ = (∑ b : CountState N → Bool, flowTableRate f b*(policyArrival 1 (countDecision b) n k*(1-countDecision b n k)))*
        prefixCoefficient μ q n k := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ = _ := by rw [hs]

end ThresholdHC.StoppingProgram
