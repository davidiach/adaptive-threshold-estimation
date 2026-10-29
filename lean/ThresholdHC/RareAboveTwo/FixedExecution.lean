import ThresholdHC.RareAboveTwo.FixedModel
import ThresholdHC.BlindUpper.CallConsumes

/-! Exact finite execution, fresh-label accounting and the full padded process path. -/

noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory ProbabilityTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open scoped ENNReal

def fixedStatePolicy (a ρ : ℝ) (N : ℕ) (r : RareSeed) (s : FixedState) (xs : List Bool) : Option ℕ :=
  fixedLabel N (fixedRun a ρ N r s xs)

inductive FixedConsumes (a ρ : ℝ) (N : ℕ) (r : RareSeed) :
    FixedState → (ℕ → ℕ → Bool) → List Bool → FixedState → (ℕ → ℕ → Bool) → Prop
  | nil (st : FixedState) (s : ℕ → ℕ → Bool) : FixedConsumes a ρ N r st s [] st s
  | cons {st st' : FixedState} {s s' : ℕ → ℕ → Bool} {j : ℕ} {b : Bool} {xs : List Bool}
      (action : fixedLabel N st = some j) (bit : s j 0 = b)
      (rest : FixedConsumes a ρ N r (fixedStep a ρ N r st b)
        (Function.update s j (tapeDrop 1 (s j))) xs st' s') :
      FixedConsumes a ρ N r st s (b::xs) st' s'

theorem FixedConsumes.state_eq {a ρ : ℝ} {N : ℕ} {r : RareSeed} {st st' : FixedState}
    {s s' : ℕ → ℕ → Bool} {xs : List Bool} (h : FixedConsumes a ρ N r st s xs st' s') :
    fixedRun a ρ N r st xs = st' := by
  induction h with
  | nil => rfl
  | cons ha hb rest ih => exact ih

theorem FixedConsumes.append {a ρ : ℝ} {N : ℕ} {r : RareSeed} {st mid last : FixedState}
    {s t u : ℕ → ℕ → Bool} {xs ys : List Bool}
    (h : FixedConsumes a ρ N r st s xs mid t) (h' : FixedConsumes a ρ N r mid t ys last u) :
    FixedConsumes a ρ N r st s (xs++ys) last u := by
  induction h with
  | nil => exact h'
  | cons ha hb rest ih => exact .cons ha hb (ih h')

theorem FixedConsumes.path_eq {a ρ : ℝ} {N : ℕ} {r : RareSeed} {st st' : FixedState}
    {s s' : ℕ → ℕ → Bool} {xs : List Bool} (h : FixedConsumes a ρ N r st s xs st' s')
    (ht : fixedLabel N st' = none) :
    populationPath (fixedStatePolicy a ρ N r st) s = fun n => xs[n]? := by
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
      change populationPath (fixedStatePolicy a ρ N r (fixedStep a ρ N r st b))
        (Function.update s j (tapeDrop 1 (s j))) n = _
      rw [ih ht]
      rfl

theorem fixedConsumes_call_prefix (a ρ : ℝ) (N : ℕ) (r : RareSeed) (ws : List (List Bool))
    (s : ℕ → ℕ → Bool) (hws : ws.length < N) (n : ℕ)
    (hn : n ≤ coupledCost a ρ (r ws.length) (s ws.length)) :
    FixedConsumes a ρ N r (ws,[]) s (tapeWord n (s ws.length))
      (fixedRun a ρ N r (ws,[]) (tapeWord n (s ws.length)))
      (Function.update s ws.length (tapeDrop n (s ws.length))) := by
  induction n with
  | zero =>
    have hd : tapeDrop 0 (s ws.length) = s ws.length := by funext k; simp [tapeDrop]
    simp only [hd,Function.update_eq_self,tapeWord,List.ofFn_zero,fixedRun,List.foldl_nil]
    exact .nil _ _
  | succ n ih =>
    have hprev := ih (by omega)
    have hs := fixedRun_call_partial a ρ N r ws hws (s ws.length) n (by omega)
    rw [hs] at hprev
    have hsingle : FixedConsumes a ρ N r (ws,tapeWord n (s ws.length))
        (Function.update s ws.length (tapeDrop n (s ws.length))) [s ws.length n]
        (fixedStep a ρ N r (ws,tapeWord n (s ws.length)) (s ws.length n))
        (Function.update s ws.length (tapeDrop (n+1) (s ws.length))) := by
      rw [← updated_tape_advance]
      exact .cons (by simp [fixedLabel,hws]) (by simp [tapeDrop]) (.nil _ _)
    have h := hprev.append hsingle
    rw [← tapeWord_succ] at h
    convert h using 1
    rw [tapeWord_succ,fixedRun_append,hs]
    rfl

theorem fixedConsumes_call (a ρ : ℝ) (N : ℕ) (r : RareSeed) (ws : List (List Bool))
    (s : ℕ → ℕ → Bool) (hws : ws.length < N) :
    FixedConsumes a ρ N r (ws,[]) s (tapeWord (coupledCost a ρ (r ws.length) (s ws.length)) (s ws.length))
      (ws++[tapeWord (coupledCost a ρ (r ws.length) (s ws.length)) (s ws.length)],[])
      (Function.update s ws.length (tapeDrop (coupledCost a ρ (r ws.length) (s ws.length)) (s ws.length))) := by
  have h := fixedConsumes_call_prefix a ρ N r ws s hws
    (coupledCost a ρ (r ws.length) (s ws.length)) le_rfl
  rw [fixedRun_call_complete a ρ N r ws hws] at h
  exact h

def fixedCallWord (a ρ : ℝ) (r : RareSeed) (s : ℕ → ℕ → Bool) (j : ℕ) : List Bool :=
  tapeWord (coupledCost a ρ (r j) (s j)) (s j)

def fixedCallWords (a ρ : ℝ) (r : RareSeed) (s : ℕ → ℕ → Bool) (n : ℕ) : List (List Bool) :=
  List.ofFn (fun i : Fin n => fixedCallWord a ρ r s i.val)

@[simp] theorem fixedCallWords_length (a ρ : ℝ) (r : RareSeed) (s : ℕ → ℕ → Bool) (n : ℕ) :
    (fixedCallWords a ρ r s n).length = n := List.length_ofFn

theorem fixedCallWords_succ (a ρ : ℝ) (r : RareSeed) (s : ℕ → ℕ → Bool) (n : ℕ) :
    fixedCallWords a ρ r s (n+1) = fixedCallWords a ρ r s n++[fixedCallWord a ρ r s n] := by
  unfold fixedCallWords
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]

def fixedTranscript (a ρ : ℝ) (r : RareSeed) (s : ℕ → ℕ → Bool) (n : ℕ) : List Bool :=
  (fixedCallWords a ρ r s n).flatten

theorem fixedTranscript_succ (a ρ : ℝ) (r : RareSeed) (s : ℕ → ℕ → Bool) (n : ℕ) :
    fixedTranscript a ρ r s (n+1) = fixedTranscript a ρ r s n++fixedCallWord a ρ r s n := by
  simp [fixedTranscript,fixedCallWords_succ]

def usedRareTapes (a ρ : ℝ) (r : RareSeed) (s : ℕ → ℕ → Bool) (n : ℕ) : ℕ → ℕ → Bool :=
  fun j => if j<n then tapeDrop (coupledCost a ρ (r j) (s j)) (s j) else s j

@[simp] theorem usedRareTapes_self (a ρ : ℝ) (r : RareSeed) (s : ℕ → ℕ → Bool) (n : ℕ) :
    usedRareTapes a ρ r s n n = s n := by simp [usedRareTapes]

theorem usedRareTapes_succ (a ρ : ℝ) (r : RareSeed) (s : ℕ → ℕ → Bool) (n : ℕ) :
    Function.update (usedRareTapes a ρ r s n) n (tapeDrop (coupledCost a ρ (r n) (s n)) (s n)) =
      usedRareTapes a ρ r s (n+1) := by
  funext j
  by_cases hj : j=n
  · subst j
    simp [usedRareTapes]
  · rw [Function.update_of_ne hj]
    simp only [usedRareTapes]
    split_ifs <;> first | rfl | omega

theorem fixedConsumes_prefix (a ρ : ℝ) (N : ℕ) (r : RareSeed) (s : ℕ → ℕ → Bool)
    (n : ℕ) (hn : n ≤ N) :
    FixedConsumes a ρ N r ([],[]) s (fixedTranscript a ρ r s n)
      (fixedCallWords a ρ r s n,[]) (usedRareTapes a ρ r s n) := by
  induction n with
  | zero =>
    have hz : usedRareTapes a ρ r s 0 = s := by funext j; simp [usedRareTapes]
    rw [hz]
    simpa only [fixedTranscript,fixedCallWords,List.ofFn_zero,List.flatten_nil]
      using (FixedConsumes.nil (a := a) (ρ := ρ) (N := N) (r := r) ([],[]) s)
  | succ n ih =>
    have hc := fixedConsumes_call a ρ N r (fixedCallWords a ρ r s n) (usedRareTapes a ρ r s n)
      (by simp only [fixedCallWords_length]; omega)
    simp only [fixedCallWords_length,usedRareTapes_self,usedRareTapes_succ] at hc
    change FixedConsumes a ρ N r (fixedCallWords a ρ r s n,[]) (usedRareTapes a ρ r s n)
      (fixedCallWord a ρ r s n) (fixedCallWords a ρ r s n++[fixedCallWord a ρ r s n],[])
      (usedRareTapes a ρ r s (n+1)) at hc
    rw [fixedTranscript_succ,fixedCallWords_succ]
    exact (ih (by omega)).append hc

theorem fixed_populationPath_eq (a ρ : ℝ) (N : ℕ) (r : RareSeed) (s : ℕ → ℕ → Bool) :
    populationPath (fixedPolicy a ρ N r) s = fun j => (fixedTranscript a ρ r s N)[j]? :=
  (fixedConsumes_prefix a ρ N r s N le_rfl).path_eq (by simp [fixedLabel])

end ThresholdHC.RareAboveTwo
