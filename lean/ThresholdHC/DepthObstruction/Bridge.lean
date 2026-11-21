import ThresholdHC.DepthObstruction.Specification

/-! The history-count form of a per-coin cap, used by
`RestrictedRMS.three_flip_coefficient_iff`, implies `PerCoinCap`. Whenever the
policy queries label `j` after the observed history `xs`, fewer than `N` earlier
queries along `xs` went to `j`. Then on every history at most `N` queries went to
each label, and the simulation never charges a label more than `N` flips. -/

noncomputable section
namespace ThresholdHC.DepthObstruction
open ThresholdHC.CriticalEntropy

/-- The number of queries to label `i` along the history `h`. -/
def historyCount (pol : List Bool → Option ℕ) (h : List Bool) (i : ℕ) : ℕ :=
  (List.range h.length).countP (fun k => decide (pol (h.take k) = some i))

theorem historyCount_append (pol : List Bool → Option ℕ) (h : List Bool) (b : Bool) (i : ℕ) :
    historyCount pol (h ++ [b]) i = historyCount pol h i + if pol h = some i then 1 else 0 := by
  unfold historyCount
  rw [List.length_append, List.length_singleton, List.range_succ, List.countP_append]
  congr 1
  · apply List.countP_congr
    intro k hk
    rw [List.mem_range] at hk
    rw [List.take_append_of_le_length hk.le]
  · simp [List.take_left']

theorem historyCount_le (pol : List Bool → Option ℕ) (N : ℕ)
    (hcap : ∀ xs j, pol xs = some j → historyCount pol xs j < N) (h : List Bool) (i : ℕ) :
    historyCount pol h i ≤ N := by
  induction h using List.reverseRecOn with
  | nil => simp [historyCount]
  | append_singleton h b ih =>
    rw [historyCount_append]
    by_cases hp : pol h = some i
    · rw [ite_eq_left hp]
      exact Nat.succ_le_of_lt (hcap h i hp)
    · rw [ite_eq_right hp, add_zero]
      exact ih

/-- Earlier queries along a history plus later simulated flips stay within the cap. -/
theorem historyCount_simulation (pol : List Bool → Option ℕ) (N : ℕ)
    (hcap : ∀ xs j, pol xs = some j → historyCount pol xs j < N) :
    ∀ (n : ℕ) (h : List Bool) (s : ℕ → ℕ → Bool) (i : ℕ),
      historyCount pol h i + (populationSimulation (fun xs => pol (h ++ xs)) n s).1 i ≤ N := by
  intro n
  induction n with
  | zero =>
    intro h s i
    simpa [populationSimulation] using historyCount_le pol N hcap h i
  | succ n ih =>
    intro h s i
    cases hp : pol h with
    | none =>
      have hsim : (populationSimulation (fun xs => pol (h ++ xs)) (n+1) s).1 i = 0 := by
        simp [populationSimulation, hp]
      rw [hsim, add_zero]
      exact historyCount_le pol N hcap h i
    | some j =>
      have hsim : (populationSimulation (fun xs => pol (h ++ xs)) (n+1) s).1 i =
          (populationSimulation (fun xs => pol ((h ++ [s j 0]) ++ xs)) n
            (Function.update s j (tapeDrop 1 (s j)))).1 i + if j = i then 1 else 0 := by
        simp [populationSimulation, hp]
      have hrec := ih (h ++ [s j 0]) (Function.update s j (tapeDrop 1 (s j))) i
      rw [historyCount_append, hp] at hrec
      rw [hsim]
      by_cases hji : j = i
      · simp only [hji, ite_true] at hrec ⊢
        omega
      · have hne : (some j = some i) = False := by simp [hji]
        simp only [hji, hne, ite_false, add_zero] at hrec ⊢
        exact hrec

/-- The bridge from the history-count cap to `PerCoinCap`. -/
theorem historyCapBridge : HistoryCapBridgeStatement := by
  intro R _ A N hcap r n s i
  have h := historyCount_simulation (A.policy r) N (fun xs j hj => hcap r xs j hj) n [] s i
  simpa [historyCount] using h

end ThresholdHC.DepthObstruction
