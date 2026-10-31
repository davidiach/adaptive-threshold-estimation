import ThresholdHC.StoppingProgram.WordStopping

/-! Pointwise expansion of table-call outputs and work into observable
finite-prefix indicators. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy
open ThresholdHC.Tier6 (Gap SignLaw)
open ThresholdHC.ObservableSimulation

theorem tableValue_word_expansion {N : ℕ} (hN : 0 < N) (b : CountState N → Bool)
    (hb : b (rootState N) = false) (ht : ∀ s : CountState N, s.1.val = N → b s = true)
    (y : CountState N → ℝ) (ω : ℕ → Bool) :
    tableValue b y ω = ∑ n ∈ Finset.range (N+1),
      wordArrival b (tapePrefix n ω)*countDecision b n (wordHeads (tapePrefix n ω))*
        arrayAt y n (wordHeads (tapePrefix n ω)) := by
  have he (n : ℕ) (hn : n ∈ Finset.range (N+1)) :
      wordArrival b (tapePrefix n ω)*countDecision b n (wordHeads (tapePrefix n ω))*
        arrayAt y n (wordHeads (tapePrefix n ω)) =
      (if tableCost b ω = n then 1 else 0)*arrayAt y n (wordHeads (tapePrefix n ω)) := by
    rw [wordStop_tape_indicator hN b hb ht ω n (by have h := Finset.mem_range.mp hn; omega)]
  rw [Finset.sum_congr rfl he,Finset.sum_eq_single (tableCost b ω)]
  · simp only [ite_true,one_mul]
    rfl
  · intro n _ hn
    simp only [Ne.symm hn,ite_false,zero_mul]
  · intro h
    have hcost := tableCall_cost_le hN b y ω
    have hmem : tableCost b ω ∈ Finset.range (N+1) := by
      apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le hcost
    exact False.elim (h hmem)

theorem tableValue_sq {N : ℕ} (b : CountState N → Bool) (y : CountState N → ℝ) (ω : ℕ → Bool) :
    (tableValue b y ω)^2 = tableValue b (fun s => (y s)^2) ω := by
  rw [tableValue_eq,tableValue_eq]

theorem wordContinue_tape_indicator {N : ℕ} (hN : 0 < N) (b : CountState N → Bool)
    (hb : b (rootState N) = false) (ht : ∀ s : CountState N, s.1.val = N → b s = true)
    (ω : ℕ → Bool) (n : ℕ) (hn : n ≤ N) :
    wordArrival b (tapePrefix n ω)*(1-countDecision b n (wordHeads (tapePrefix n ω))) =
      if n < tableCost b ω then 1 else 0 := by
  have ha := wordArrival_tape_indicator b hb ω n hn
  have hs := wordStop_tape_indicator hN b hb ht ω n hn
  by_cases hlt : n < tableCost b ω
  · rw [ite_eq_left hlt]
    rw [ite_eq_left hlt.le] at ha
    rw [ite_eq_right (by omega)] at hs
    nlinarith
  · rw [ite_eq_right hlt]
    by_cases he : tableCost b ω = n
    · rw [ite_eq_left he.ge] at ha
      rw [ite_eq_left he] at hs
      nlinarith
    · rw [ite_eq_right (by omega)] at ha
      rw [ha,zero_mul]

theorem tableCost_word_expansion {N : ℕ} (hN : 0 < N) (b : CountState N → Bool)
    (hb : b (rootState N) = false) (ht : ∀ s : CountState N, s.1.val = N → b s = true)
    (ω : ℕ → Bool) :
    (tableCost b ω:ℝ) = ∑ n ∈ Finset.range (N+1),
      wordArrival b (tapePrefix n ω)*(1-countDecision b n (wordHeads (tapePrefix n ω))) := by
  have he (n : ℕ) (hn : n ∈ Finset.range (N+1)) :
      wordArrival b (tapePrefix n ω)*(1-countDecision b n (wordHeads (tapePrefix n ω))) =
        if n < tableCost b ω then 1 else 0 :=
    wordContinue_tape_indicator hN b hb ht ω n (by have h := Finset.mem_range.mp hn; omega)
  rw [Finset.sum_congr rfl he,Finset.sum_boole]
  have hset : (Finset.range (N+1)).filter (fun n => n < tableCost b ω) = Finset.range (tableCost b ω) := by
    ext n
    have hc : tableCost b ω ≤ N := tableCall_cost_le hN b (fun _ => 0) ω
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [hset,Finset.card_range]

theorem population_prefix_integrable (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (n : ℕ) (F : (Fin n → Bool) → ℝ) :
    Integrable (fun ω => F (tapePrefix n ω)) (originalPopulationTapeLaw μ q) := by
  apply Integrable.of_bound ((measurable_of_countable F).comp (measurable_prefix n)).aestronglyMeasurable
    (∑ w, ‖F w‖)
  exact Filter.Eventually.of_forall (fun ω => Finset.single_le_sum (fun _ _ => norm_nonneg _)
    (Finset.mem_univ (tapePrefix n ω)))

end ThresholdHC.StoppingProgram
