import ThresholdHC.StoppingProgram.FlowMixture
import ThresholdHC.EntropyTailExecution.CallMachine
import ThresholdHC.EntropyTailUpper.BoundedSearch

/-! Deterministic count tables as actual observable positive finite calls.
The call reads only the observed word and always stops by its supplied cap. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy
open ThresholdHC.EntropyTailUpper ThresholdHC.EntropyTailExecution

theorem wordHeads_le_length {n : ℕ} (w : Fin n → Bool) : wordHeads w ≤ n := by
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin n)

def tableHit {N : ℕ} (b : CountState N → Bool) (n : ℕ) (w : Fin n → Bool) : Prop :=
  0 < n ∧ countDecision b n (wordHeads w) = 1

def tableCost {N : ℕ} (b : CountState N → Bool) : (ℕ → Bool) → ℕ := prefixSearchCost (tableHit b) N

theorem tableCost_positive {N : ℕ} (hN : 0 < N) (b : CountState N → Bool) (ω : ℕ → Bool) :
    0 < tableCost b ω := by
  have h := (boundedFirst_spec (fun n => tableHit b n (tapePrefix n ω)) N).2
  change tableHit b (tableCost b ω) (tapePrefix (tableCost b ω) ω) ∨ tableCost b ω = N at h
  rcases h with h | h
  · exact h.1
  · omega

def tableValue {N : ℕ} (b : CountState N → Bool) (y : CountState N → ℝ) : (ℕ → Bool) → ℝ :=
  prefixSearchValue (tableHit b) (fun n w => arrayAt y n (wordHeads w)) N

def tableCall {N : ℕ} (hN : 0 < N) (b : CountState N → Bool) (y : CountState N → ℝ) : FiniteCall where
  cost := tableCost b
  value := tableValue b y
  measurable_cost := measurable_prefixSearchCost _ _
  measurable_value := measurable_prefixSearchValue _ _ _
  positive := tableCost_positive hN b
  prefix_ext := fun ω ω' he => ⟨prefixSearchCost_ext _ _ ω ω' he,prefixSearchValue_ext _ _ _ ω ω' he⟩

theorem tableCall_cost_le {N : ℕ} (hN : 0 < N) (b : CountState N → Bool) (y : CountState N → ℝ)
    (ω : ℕ → Bool) : (tableCall hN b y).cost ω ≤ N := prefixSearchCost_le _ _ _

def tableStoppedState {N : ℕ} (b : CountState N → Bool) (ω : ℕ → Bool) : CountState N :=
  ⟨⟨tableCost b ω,by
      have h : tableCost b ω ≤ N := prefixSearchCost_le (tableHit b) N ω
      exact Nat.lt_succ_of_le h⟩,
    ⟨wordHeads (tapePrefix (tableCost b ω) ω),by
      have h := wordHeads_le_length (tapePrefix (tableCost b ω) ω)
      exact Nat.lt_succ_of_le h⟩⟩

theorem tableValue_eq {N : ℕ} (b : CountState N → Bool) (y : CountState N → ℝ) (ω : ℕ → Bool) :
    tableValue b y ω = y (tableStoppedState b ω) := arrayAt_state y (tableStoppedState b ω)

theorem tableValue_bounded {N : ℕ} (b : CountState N → Bool) (y : CountState N → ℝ) (ω : ℕ → Bool) :
    ‖tableValue b y ω‖ ≤ ∑ s, ‖y s‖ := by
  rw [tableValue_eq]
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ _)

theorem boundedFirst_eq_iff (hit : ℕ → Prop) (M n : ℕ) :
    boundedFirst hit M = n ↔ n ≤ M ∧ (hit n ∨ n = M) ∧ ∀ k, k < n → ¬hit k := by
  constructor
  · rintro rfl
    exact ⟨(boundedFirst_spec hit M).1,(boundedFirst_spec hit M).2,boundedFirst_before hit M⟩
  · rintro ⟨hn,hh,hbefore⟩
    have hle : boundedFirst hit M ≤ n := by
      rcases hh with hh | hh
      · exact boundedFirst_le_of_hit hit M n hh
      · rw [hh]
        exact (boundedFirst_spec hit M).1
    apply le_antisymm hle
    by_contra hge
    have hlt : boundedFirst hit M < n := lt_of_not_ge hge
    rcases (boundedFirst_spec hit M).2 with hhit | hcap
    · exact hbefore _ hlt hhit
    · omega

theorem tableCost_eq_iff {N : ℕ} (b : CountState N → Bool) (ω : ℕ → Bool) (n : ℕ) :
    tableCost b ω = n ↔ n ≤ N ∧ (tableHit b n (tapePrefix n ω) ∨ n = N) ∧
      ∀ k, k < n → ¬tableHit b k (tapePrefix k ω) := boundedFirst_eq_iff _ _ _

end ThresholdHC.StoppingProgram
