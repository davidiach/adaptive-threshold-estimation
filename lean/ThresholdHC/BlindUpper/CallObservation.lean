import ThresholdHC.BlindUpper.PaddedCall

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier2

instance boolListMeasurableSpace : MeasurableSpace (List Bool) := ⊤

/-- Canonical completion used only to evaluate a rule on its observed prefix. -/
def completeList (xs : List Bool) : ℕ → Bool := fun n => xs.getD n false

theorem measurable_completeList : Measurable completeList := measurable_of_countable _

def tapeWord (n : ℕ) (ω : ℕ → Bool) : List Bool := List.ofFn (tapePrefix n ω)

@[simp] theorem tapeWord_length (n : ℕ) (ω : ℕ → Bool) : (tapeWord n ω).length = n :=
  List.length_ofFn

theorem completeList_tapeWord_prefix (n : ℕ) (ω : ℕ → Bool) :
    tapePrefix n (completeList (tapeWord n ω)) = tapePrefix n ω := by
  funext i
  simp [completeList,tapeWord,tapePrefix,List.getD_eq_getElem?_getD,i.isLt]

/-- Completion does not allow a stopped rule to inspect an unseen flip. -/
theorem finiteCall_ready_iff {R : Type} (cost : R × (ℕ → Bool) → ℕ)
    (hext : ∀ r ω ω', tapePrefix (cost (r,ω)) ω = tapePrefix (cost (r,ω)) ω' →
      cost (r,ω') = cost (r,ω)) (r : R) (ω : ℕ → Bool) (n : ℕ) :
    cost (r,completeList (tapeWord n ω)) ≤ n ↔ cost (r,ω) ≤ n := by
  have hp := completeList_tapeWord_prefix n ω
  constructor
  · intro h
    have hc := hext r (completeList (tapeWord n ω)) ω (prefix_eq_restrict hp h)
    exact hc ▸ h
  · intro h
    have hc := hext r ω (completeList (tapeWord n ω)) (prefix_eq_restrict hp.symm h)
    exact hc.symm ▸ h

theorem paddedCutoff_ready_iff (L l n : ℕ) (ω : ℕ → Bool) :
    paddedCutoffCost L (l,completeList (tapeWord n ω)) ≤ n ↔ paddedCutoffCost L (l,ω) ≤ n :=
  finiteCall_ready_iff (paddedCutoffCost L)
    (fun r ω ω' h => (paddedCutoff_prefix_ext L r ω ω' h).1) l ω n

theorem paddedCutoff_observed_value (L l n : ℕ) (ω : ℕ → Bool)
    (h : paddedCutoffCost L (l,ω) ≤ n) :
    cutoffValue L (l,completeList (tapeWord n ω)) = cutoffValue L (l,ω) :=
  (paddedCutoff_prefix_ext L l ω _
    (prefix_eq_restrict (completeList_tapeWord_prefix n ω).symm h)).2

def observedCutoffDone (L l : ℕ) (xs : List Bool) : Bool :=
  decide (paddedCutoffCost L (l,completeList xs) ≤ xs.length)

theorem observedCutoffDone_word (L l n : ℕ) (ω : ℕ → Bool) :
    observedCutoffDone L l (tapeWord n ω) = decide (paddedCutoffCost L (l,ω) ≤ n) := by
  simp only [observedCutoffDone,tapeWord_length,paddedCutoff_ready_iff]

theorem observedCutoffDone_empty (L l : ℕ) : observedCutoffDone L l [] = false := by
  have h := (paddedCutoffCost_bounds L (l,completeList [])).1
  simp only [observedCutoffDone,List.length_nil]
  simp [show ¬paddedCutoffCost L (l,completeList []) ≤ 0 by omega]

end ThresholdHC.BlindUpper
