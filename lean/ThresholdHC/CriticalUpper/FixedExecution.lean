import ThresholdHC.CriticalUpper.FixedModel
import ThresholdHC.BlindUpper.CallConsumes

/-! Exact finite execution, fresh-label accounting and the full padded process path. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory ProbabilityTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open scoped ENNReal

def fixedStatePolicy (ρ : ℝ) (N : ℕ) (r : CriticalSeed) (s : FixedState) (xs : List Bool) : Option ℕ :=
  fixedLabel N (fixedRun ρ N r s xs)

inductive FixedConsumes (ρ : ℝ) (N : ℕ) (r : CriticalSeed) :
    FixedState → (ℕ → ℕ → Bool) → List Bool → FixedState → (ℕ → ℕ → Bool) → Prop
  | nil (st : FixedState) (s : ℕ → ℕ → Bool) : FixedConsumes ρ N r st s [] st s
  | cons {st st' : FixedState} {s s' : ℕ → ℕ → Bool} {j : ℕ} {b : Bool} {xs : List Bool}
      (action : fixedLabel N st = some j) (bit : s j 0 = b)
      (rest : FixedConsumes ρ N r (fixedStep ρ N r st b)
        (Function.update s j (tapeDrop 1 (s j))) xs st' s') :
      FixedConsumes ρ N r st s (b::xs) st' s'

theorem FixedConsumes.state_eq {ρ : ℝ} {N : ℕ} {r : CriticalSeed} {st st' : FixedState}
    {s s' : ℕ → ℕ → Bool} {xs : List Bool} (h : FixedConsumes ρ N r st s xs st' s') :
    fixedRun ρ N r st xs = st' := by
  induction h with
  | nil => rfl
  | cons ha hb rest ih => exact ih

theorem FixedConsumes.append {ρ : ℝ} {N : ℕ} {r : CriticalSeed} {st mid last : FixedState}
    {s t u : ℕ → ℕ → Bool} {xs ys : List Bool}
    (h : FixedConsumes ρ N r st s xs mid t) (h' : FixedConsumes ρ N r mid t ys last u) :
    FixedConsumes ρ N r st s (xs++ys) last u := by
  induction h with
  | nil => exact h'
  | cons ha hb rest ih => exact .cons ha hb (ih h')

theorem FixedConsumes.path_eq {ρ : ℝ} {N : ℕ} {r : CriticalSeed} {st st' : FixedState}
    {s s' : ℕ → ℕ → Bool} {xs : List Bool} (h : FixedConsumes ρ N r st s xs st' s')
    (ht : fixedLabel N st' = none) :
    populationPath (fixedStatePolicy ρ N r st) s = fun n => xs[n]? := by
  induction h with
  | nil st s =>
    rw [populationPath_none _ _ ht]
    rfl
  | @cons st st' s s' j b xs ha hb rest ih =>
    funext n
    cases n with
    | zero => simp [populationPath_zero,fixedStatePolicy,fixedRun,ha,hb]
    | succ n =>
      rw [populationPath_succ _ _ j n ha,hb]
      change populationPath (fixedStatePolicy ρ N r (fixedStep ρ N r st b))
        (Function.update s j (tapeDrop 1 (s j))) n = _
      rw [ih ht]
      rfl

theorem fixedConsumes_call_prefix (ρ : ℝ) (N : ℕ) (r : CriticalSeed) (ws : List (List Bool))
    (s : ℕ → ℕ → Bool) (hws : ws.length < N) (n : ℕ)
    (hn : n ≤ coupledCost ρ (r ws.length) (s ws.length)) :
    FixedConsumes ρ N r (ws,[]) s (tapeWord n (s ws.length))
      (fixedRun ρ N r (ws,[]) (tapeWord n (s ws.length)))
      (Function.update s ws.length (tapeDrop n (s ws.length))) := by
  induction n with
  | zero =>
    have hd : tapeDrop 0 (s ws.length) = s ws.length := by funext k; simp [tapeDrop]
    simp only [hd,Function.update_eq_self,tapeWord,List.ofFn_zero,fixedRun,List.foldl_nil]
    exact .nil _ _
  | succ n ih =>
    have hprev := ih (by omega)
    have hs := fixedRun_call_partial ρ N r ws hws (s ws.length) n (by omega)
    rw [hs] at hprev
    have hsingle : FixedConsumes ρ N r (ws,tapeWord n (s ws.length))
        (Function.update s ws.length (tapeDrop n (s ws.length))) [s ws.length n]
        (fixedStep ρ N r (ws,tapeWord n (s ws.length)) (s ws.length n))
        (Function.update s ws.length (tapeDrop (n+1) (s ws.length))) := by
      rw [← updated_tape_advance]
      exact .cons (by simp [fixedLabel,hws]) (by simp [tapeDrop]) (.nil _ _)
    have h := hprev.append hsingle
    rw [← tapeWord_succ] at h
    convert h using 1
    rw [tapeWord_succ,fixedRun_append,hs]
    rfl

theorem fixedConsumes_call (ρ : ℝ) (N : ℕ) (r : CriticalSeed) (ws : List (List Bool))
    (s : ℕ → ℕ → Bool) (hws : ws.length < N) :
    FixedConsumes ρ N r (ws,[]) s (tapeWord (coupledCost ρ (r ws.length) (s ws.length)) (s ws.length))
      (ws++[tapeWord (coupledCost ρ (r ws.length) (s ws.length)) (s ws.length)],[])
      (Function.update s ws.length (tapeDrop (coupledCost ρ (r ws.length) (s ws.length)) (s ws.length))) := by
  have h := fixedConsumes_call_prefix ρ N r ws s hws
    (coupledCost ρ (r ws.length) (s ws.length)) le_rfl
  rw [fixedRun_call_complete ρ N r ws hws] at h
  exact h

def fixedCallWord (ρ : ℝ) (r : CriticalSeed) (s : ℕ → ℕ → Bool) (j : ℕ) : List Bool :=
  tapeWord (coupledCost ρ (r j) (s j)) (s j)

def fixedCallWords (ρ : ℝ) (r : CriticalSeed) (s : ℕ → ℕ → Bool) (n : ℕ) : List (List Bool) :=
  List.ofFn (fun i : Fin n => fixedCallWord ρ r s i.val)

@[simp] theorem fixedCallWords_length (ρ : ℝ) (r : CriticalSeed) (s : ℕ → ℕ → Bool) (n : ℕ) :
    (fixedCallWords ρ r s n).length = n := List.length_ofFn

theorem fixedCallWords_succ (ρ : ℝ) (r : CriticalSeed) (s : ℕ → ℕ → Bool) (n : ℕ) :
    fixedCallWords ρ r s (n+1) = fixedCallWords ρ r s n++[fixedCallWord ρ r s n] := by
  unfold fixedCallWords
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]

def fixedTranscript (ρ : ℝ) (r : CriticalSeed) (s : ℕ → ℕ → Bool) (n : ℕ) : List Bool :=
  (fixedCallWords ρ r s n).flatten

theorem fixedTranscript_succ (ρ : ℝ) (r : CriticalSeed) (s : ℕ → ℕ → Bool) (n : ℕ) :
    fixedTranscript ρ r s (n+1) = fixedTranscript ρ r s n++fixedCallWord ρ r s n := by
  simp [fixedTranscript,fixedCallWords_succ]

def usedCriticalTapes (ρ : ℝ) (r : CriticalSeed) (s : ℕ → ℕ → Bool) (n : ℕ) : ℕ → ℕ → Bool :=
  fun j => if j<n then tapeDrop (coupledCost ρ (r j) (s j)) (s j) else s j

@[simp] theorem usedCriticalTapes_self (ρ : ℝ) (r : CriticalSeed) (s : ℕ → ℕ → Bool) (n : ℕ) :
    usedCriticalTapes ρ r s n n = s n := by simp [usedCriticalTapes]

theorem usedCriticalTapes_succ (ρ : ℝ) (r : CriticalSeed) (s : ℕ → ℕ → Bool) (n : ℕ) :
    Function.update (usedCriticalTapes ρ r s n) n (tapeDrop (coupledCost ρ (r n) (s n)) (s n)) =
      usedCriticalTapes ρ r s (n+1) := by
  funext j
  by_cases hj : j=n
  · subst j
    simp [usedCriticalTapes]
  · rw [Function.update_of_ne hj]
    simp only [usedCriticalTapes]
    split_ifs <;> first | rfl | omega

theorem fixedConsumes_prefix (ρ : ℝ) (N : ℕ) (r : CriticalSeed) (s : ℕ → ℕ → Bool)
    (n : ℕ) (hn : n ≤ N) :
    FixedConsumes ρ N r ([],[]) s (fixedTranscript ρ r s n)
      (fixedCallWords ρ r s n,[]) (usedCriticalTapes ρ r s n) := by
  induction n with
  | zero =>
    have hz : usedCriticalTapes ρ r s 0 = s := by funext j; simp [usedCriticalTapes]
    rw [hz]
    simpa only [fixedTranscript,fixedCallWords,List.ofFn_zero,List.flatten_nil]
      using (FixedConsumes.nil (ρ := ρ) (N := N) (r := r) ([],[]) s)
  | succ n ih =>
    have hc := fixedConsumes_call ρ N r (fixedCallWords ρ r s n) (usedCriticalTapes ρ r s n)
      (by simp only [fixedCallWords_length]; omega)
    simp only [fixedCallWords_length,usedCriticalTapes_self,usedCriticalTapes_succ] at hc
    change FixedConsumes ρ N r (fixedCallWords ρ r s n,[]) (usedCriticalTapes ρ r s n)
      (fixedCallWord ρ r s n) (fixedCallWords ρ r s n++[fixedCallWord ρ r s n],[])
      (usedCriticalTapes ρ r s (n+1)) at hc
    rw [fixedTranscript_succ,fixedCallWords_succ]
    exact (ih (by omega)).append hc

theorem fixed_populationPath_eq (ρ : ℝ) (N : ℕ) (r : CriticalSeed) (s : ℕ → ℕ → Bool) :
    populationPath (fixedPolicy ρ N r) s = fun j => (fixedTranscript ρ r s N)[j]? :=
  (fixedConsumes_prefix ρ N r s N le_rfl).path_eq (by simp [fixedLabel])

end ThresholdHC.CriticalUpper
