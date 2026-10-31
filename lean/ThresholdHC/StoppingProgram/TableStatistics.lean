import ThresholdHC.StoppingProgram.TableExpansion

/-! Exact output and work moments of deterministic table calls under the
original observable population experiment. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy
open ThresholdHC.Tier6 (Gap SignLaw)
open ThresholdHC.ObservableSimulation

theorem sum_words_by_heads (n : ℕ) (A : (Fin n → Bool) → ℝ) (F : ℕ → ℝ) :
    (∑ w : Fin n → Bool, A w*F (wordHeads w)) =
      ∑ k ∈ Finset.range (n+1), (∑ w : Fin n → Bool, if wordHeads w = k then A w else 0)*F k := by
  symm
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_eq_single (wordHeads w)]
  · simp
  · intro k _ hk
    simp only [Ne.symm hk,ite_false,zero_mul]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (Nat.lt_succ_of_le (wordHeads_le_length w))))

theorem population_word_integral (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    {N : ℕ} (b : CountState N → Bool) (n : ℕ) (F : ℕ → ℝ) :
    (∫ ω, wordArrival b (tapePrefix n ω)*F (wordHeads (tapePrefix n ω)) ∂originalPopulationTapeLaw μ q) =
      ∑ k ∈ Finset.range (n+1), policyArrival 1 (countDecision b) n k*prefixCoefficient μ q n k*F k := by
  rw [population_prefix_integral μ q n (fun w => wordArrival b w*F (wordHeads w))]
  have he : (∑ w : Fin n → Bool, prefixCoefficient μ q n (wordHeads w)*(wordArrival b w*F (wordHeads w))) =
      ∑ w : Fin n → Bool, wordArrival b w*(prefixCoefficient μ q n (wordHeads w)*F (wordHeads w)) := by
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [he,sum_words_by_heads n (wordArrival b) (fun k => prefixCoefficient μ q n k*F k)]
  apply Finset.sum_congr rfl
  intro k _
  change wordArrivalCount b n k*(prefixCoefficient μ q n k*F k) = _
  rw [wordArrivalCount_eq_policyArrival]
  ring

theorem tableValue_integral {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (hN : 0 < N) (b : CountState N → Bool) (hb : b (rootState N) = false)
    (ht : ∀ s : CountState N, s.1.val = N → b s = true) (y : CountState N → ℝ) :
    (∫ ω, tableValue b y ω ∂originalPopulationTapeLaw μ q) =
      ∑ n ∈ Finset.range (N+1), ∑ k ∈ Finset.range (n+1),
        policyArrival 1 (countDecision b) n k*countDecision b n k*prefixCoefficient μ q n k*arrayAt y n k := by
  have hex : tableValue b y = fun ω => ∑ n ∈ Finset.range (N+1),
      wordArrival b (tapePrefix n ω)*(countDecision b n (wordHeads (tapePrefix n ω))*arrayAt y n (wordHeads (tapePrefix n ω))) := by
    funext ω
    rw [tableValue_word_expansion hN b hb ht]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hex,integral_finsetSum _ (fun n _ => population_prefix_integrable μ q n
    (fun w => wordArrival b w*(countDecision b n (wordHeads w)*arrayAt y n (wordHeads w))))]
  apply Finset.sum_congr rfl
  intro n _
  rw [population_word_integral μ q b n (fun k => countDecision b n k*arrayAt y n k)]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem tableCost_integral {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (hN : 0 < N) (b : CountState N → Bool) (hb : b (rootState N) = false)
    (ht : ∀ s : CountState N, s.1.val = N → b s = true) :
    (∫ ω, (tableCost b ω:ℝ) ∂originalPopulationTapeLaw μ q) =
      ∑ n ∈ Finset.range (N+1), ∑ k ∈ Finset.range (n+1),
        policyArrival 1 (countDecision b) n k*(1-countDecision b n k)*prefixCoefficient μ q n k := by
  have hex : (fun ω => (tableCost b ω:ℝ)) = fun ω => ∑ n ∈ Finset.range (N+1),
      wordArrival b (tapePrefix n ω)*(1-countDecision b n (wordHeads (tapePrefix n ω))) :=
    funext (tableCost_word_expansion hN b hb ht)
  rw [hex,integral_finsetSum _ (fun n _ => population_prefix_integrable μ q n
    (fun w => wordArrival b w*(1-countDecision b n (wordHeads w))))]
  apply Finset.sum_congr rfl
  intro n _
  rw [population_word_integral μ q b n (fun k => 1-countDecision b n k)]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem arrayAt_sq {N : ℕ} (y : CountState N → ℝ) (n k : ℕ) :
    arrayAt (fun s => (y s)^2) n k = (arrayAt y n k)^2 := by
  unfold arrayAt
  split_ifs <;> simp

theorem tableValue_second_moment {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (hN : 0 < N) (b : CountState N → Bool) (hb : b (rootState N) = false)
    (ht : ∀ s : CountState N, s.1.val = N → b s = true) (y : CountState N → ℝ) :
    (∫ ω, (tableValue b y ω)^2 ∂originalPopulationTapeLaw μ q) =
      ∑ n ∈ Finset.range (N+1), ∑ k ∈ Finset.range (n+1),
        policyArrival 1 (countDecision b) n k*countDecision b n k*prefixCoefficient μ q n k*(arrayAt y n k)^2 := by
  simp only [tableValue_sq]
  rw [tableValue_integral μ q hN b hb ht]
  simp only [arrayAt_sq]

end ThresholdHC.StoppingProgram
