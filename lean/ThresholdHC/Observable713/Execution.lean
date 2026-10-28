import ThresholdHC.Observable713.Controller
import ThresholdHC.BlindUpper.ActualBatch

/-! Pointwise execution identities: output and work equal the analyzed call. -/

noncomputable section
namespace ThresholdHC.Observable713
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper
open ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open scoped ENNReal

theorem tapeWord_cons (n : ℕ) (ω : ℕ → Bool) :
    tapeWord (n+1) ω = ω 0 :: tapeWord n (tapeDrop 1 ω) := by
  unfold tapeWord tapePrefix
  rw [List.ofFn_succ]
  simp [tapeDrop,Nat.add_comm]

/-- A policy reading exactly the first N flips of coin zero has this complete path. -/
theorem single_coin_path (N : ℕ) (pol : List Bool → Option ℕ)
    (s : ℕ → ℕ → Bool)
    (hp : ∀ n ≤ N, pol (tapeWord n (s 0)) = if n < N then some 0 else none) :
    populationPath pol s = fun n => (tapeWord N (s 0))[n]? := by
  induction N generalizing pol s with
  | zero =>
    have hh : pol [] = none := by simpa [tapeWord] using hp 0 le_rfl
    rw [populationPath_none _ _ hh]
    rfl
  | succ N ih =>
    have hh : pol [] = some 0 := by simpa [tapeWord] using hp 0 (Nat.zero_le _)
    let s' := Function.update s 0 (tapeDrop 1 (s 0))
    have hs' : s' 0 = tapeDrop 1 (s 0) := by simp [s']
    have hnext : ∀ n ≤ N, (fun xs => pol (s 0 0 :: xs)) (tapeWord n (s' 0)) =
        if n < N then some 0 else none := by
      intro n hn
      change pol (s 0 0 :: tapeWord n (s' 0)) = _
      rw [hs',← tapeWord_cons]
      simpa only [Nat.add_lt_add_iff_right] using hp (n+1) (Nat.add_le_add_right hn 1)
    have he := ih (fun xs => pol (s 0 0 :: xs)) s' hnext
    funext n
    cases n with
    | zero => simp [populationPath_zero,hh,tapeWord_cons]
    | succ n =>
      rw [populationPath_succ pol s 0 n hh]
      change populationPath (fun xs => pol (s 0 0 :: xs)) s' n = _
      rw [he,hs',tapeWord_cons]
      rfl

theorem population_path (l : ℕ) (s : ℕ → ℕ → Bool) :
    populationPath (policy l) s = fun n => (tapeWord (callCost (l,s 0)) (s 0))[n]? := by
  apply single_coin_path
  intro n hn
  rw [policy_word]
  by_cases h : callCost (l,s 0) ≤ n
  · rw [ite_eq_left h,ite_eq_right (by omega)]
  · rw [ite_eq_right h,ite_eq_left (by omega)]

theorem decoded_word_prefix (n : ℕ) (ω : ℕ → Bool) :
    tapePrefix n (decodedTape (fun k => (tapeWord n ω)[k]?)) = tapePrefix n ω := by
  funext i
  simp [tapePrefix,decodedTape,tapeWord,i.isLt]

theorem population_output (l : ℕ) (s : ℕ → ℕ → Bool) :
    output (l,populationPath (policy l) s) = callValue (l,s 0) := by
  rw [population_path]
  exact (call_prefix_ext l (s 0) _ (decoded_word_prefix _ _).symm).2

theorem population_work (l : ℕ) (s : ℕ → ℕ → Bool) :
    totalProcessWork (populationPath (policy l) s) = (callCost (l,s 0) : ℝ≥0∞) := by
  rw [population_path,totalProcessWork_word,tapeWord_length]

end ThresholdHC.Observable713
