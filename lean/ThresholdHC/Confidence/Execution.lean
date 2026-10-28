import ThresholdHC.Confidence.Controller
import ThresholdHC.BlindUpper.MachinePath

noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory
namespace ThresholdHC.Confidence
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open ThresholdHC.BlindUpper ThresholdHC.ObservableSimulation

theorem mem_activeSet {m : ℕ} (s : RepeatState m) (i : MedianIndex m) :
    i ∈ activeSet s ↔ controlLabel (s i).1 ≠ none := by
  simp [activeSet, Option.isSome_iff_ne_none]

theorem selectActive_first {m : ℕ} (s : RepeatState m) (i : MedianIndex m)
    (hi : controlLabel (s i).1 ≠ none)
    (hp : ∀ j : MedianIndex m, j < i → controlLabel (s j).1 = none) :
    selectActive s = some i := by
  have him : i ∈ activeSet s := (mem_activeSet s i).mpr hi
  have hn : (activeSet s).Nonempty := ⟨i,him⟩
  rw [selectActive, dite_eq_left hn]
  congr 1
  apply (Finset.min'_eq_iff _ _ _).mpr
  refine ⟨him, ?_⟩
  intro j hj
  by_contra hji
  exact (mem_activeSet s j).mp hj (hp j (lt_of_not_ge hji))

theorem selectActive_none_iff {m : ℕ} (s : RepeatState m) :
    selectActive s = none ↔ ∀ i, controlLabel (s i).1 = none := by
  classical
  unfold selectActive
  split_ifs with hn
  · constructor
    · intro h; cases h
    · intro h
      obtain ⟨i,hi⟩ := hn
      exact False.elim ((mem_activeSet s i).mp hi (h i))
  · simp only [true_iff]
    intro i
    by_contra hi
    exact hn ⟨i,(mem_activeSet s i).mpr hi⟩

theorem selectActive_some_mem {m : ℕ} (s : RepeatState m) (i : MedianIndex m)
    (h : selectActive s = some i) : controlLabel (s i).1 ≠ none := by
  unfold selectActive at h
  split_ifs at h with hn
  · have he := Option.some.inj h
    exact (mem_activeSet s i).mp (he ▸ Finset.min'_mem _ hn)

theorem repeatLabel_none_iff {m : ℕ} (s : RepeatState m) :
    repeatLabel s = none ↔ selectActive s = none := by
  cases hs : selectActive s with
  | none => simp [repeatLabel,hs]
  | some i =>
    have hi := selectActive_some_mem s i hs
    cases hj : controlLabel (s i).1 with
    | none => exact False.elim (hi hj)
    | some j => simp [repeatLabel,hs,hj]

theorem repeatLabel_first {m : ℕ} (s : RepeatState m) (i : MedianIndex m) (j : ℕ)
    (hi : controlLabel (s i).1 = some j)
    (hp : ∀ k : MedianIndex m, k < i → controlLabel (s k).1 = none) :
    repeatLabel s = some (Nat.pair i.val j) := by
  have hs := selectActive_first s i (by rw [hi]; simp) hp
  simp [repeatLabel,hs,hi]

theorem repeatRun_absorbs (m L : ℕ) (r : RepeatSeed) (s : RepeatState m)
    (hs : repeatLabel s = none) (xs : List Bool) : repeatRun m L r s xs = s := by
  have hn := (repeatLabel_none_iff s).mp hs
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa only [repeatRun,List.foldl_cons,repeatStep,hn] using ih

theorem repeatOutput_at_halt (m L : ℕ) (r : RepeatSeed) (x : ProcessTape) (n : ℕ)
    (hn : repeatPolicy m L r (processHistory x n) = none) :
    repeatOutput m L (r,x) = repeatControlOutput m L r
      (repeatRun m L r (repeatInitial m) (processHistory x n)) := by
  have hmark : (repeatPolicy m L r (processHistory x n)).isNone = true := by rw [hn]; rfl
  obtain ⟨k,hkn,hk⟩ := firstSuccess_finite_le
    (fun j => (repeatPolicy m L r (processHistory x j)).isNone) n hmark
  have hkstop : repeatPolicy m L r (processHistory x k) = none :=
    Option.isNone_iff_eq_none.mp ((firstSuccess_eq _ _).mp hk).1
  have he : repeatRun m L r (repeatInitial m) (processHistory x n) =
      repeatRun m L r (repeatInitial m) (processHistory x k) := by
    conv_lhs => rw [show n = k+(n-k) by omega,processHistory_add,repeatRun_append]
    exact repeatRun_absorbs m L r _ hkstop _
  change repeatControlOutput m L r (repeatRun m L r (repeatInitial m)
    (processHistory x (repeatHaltTime m L (r,x)).toNat)) = _
  rw [show repeatHaltTime m L (r,x) = k from hk]
  simp only [ENat.toNat_natCast]
  rw [he]

inductive RepeatConsumes (m L : ℕ) (r : RepeatSeed) :
    RepeatState m → (ℕ → ℕ → Bool) → List Bool → RepeatState m → (ℕ → ℕ → Bool) → Prop
  | nil (st : RepeatState m) (s : ℕ → ℕ → Bool) : RepeatConsumes m L r st s [] st s
  | cons {st st' : RepeatState m} {s s' : ℕ → ℕ → Bool} {j : ℕ} {b : Bool} {xs : List Bool}
      (action : repeatLabel st = some j) (bit : s j 0 = b)
      (rest : RepeatConsumes m L r (repeatStep m L r st b)
        (Function.update s j (tapeDrop 1 (s j))) xs st' s') :
      RepeatConsumes m L r st s (b::xs) st' s'

theorem RepeatConsumes.state_eq {m L : ℕ} {r : RepeatSeed} {st st' : RepeatState m}
    {s s' : ℕ → ℕ → Bool} {xs : List Bool} (h : RepeatConsumes m L r st s xs st' s') :
    repeatRun m L r st xs = st' := by
  induction h with
  | nil => rfl
  | cons ha hb rest ih => exact ih

theorem RepeatConsumes.append {m L : ℕ} {r : RepeatSeed} {st mid last : RepeatState m}
    {s t u : ℕ → ℕ → Bool} {xs ys : List Bool}
    (h : RepeatConsumes m L r st s xs mid t) (h' : RepeatConsumes m L r mid t ys last u) :
    RepeatConsumes m L r st s (xs++ys) last u := by
  induction h with
  | nil => exact h'
  | cons ha hb rest ih => exact .cons ha hb (ih h')

def repeatStatePolicy (m L : ℕ) (r : RepeatSeed) (s : RepeatState m) (xs : List Bool) : Option ℕ :=
  repeatLabel (repeatRun m L r s xs)

theorem RepeatConsumes.path_eq {m L : ℕ} {r : RepeatSeed} {st st' : RepeatState m}
    {s s' : ℕ → ℕ → Bool} {xs : List Bool} (h : RepeatConsumes m L r st s xs st' s')
    (ht : repeatLabel st' = none) :
    populationPath (repeatStatePolicy m L r st) s = fun n => xs[n]? := by
  induction h with
  | nil st s =>
    rw [populationPath_none _ _ ht]
    rfl
  | @cons st st' s s' j b xs ha hb rest ih =>
    funext n
    cases n with
    | zero => simp [populationPath_zero,repeatStatePolicy,repeatRun,ha,hb]
    | succ n =>
      rw [populationPath_succ _ _ j n ha,hb]
      change populationPath (repeatStatePolicy m L r (repeatStep m L r st b))
        (Function.update s j (tapeDrop 1 (s j))) n = _
      rw [ih ht]
      rfl

end ThresholdHC.Confidence
