import ThresholdHC.BlindUpper.ClassifierProcedure
import ThresholdHC.Uniform713.CoupledWork
import ThresholdHC.Uniform713.Specification

/-! The 713 classifier and shared-prefix increment, with their actual flip count. -/

noncomputable section
namespace ThresholdHC.Observable713
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.BlindUpper

def classifierCost (L : ℕ) (ω : ℕ → Bool) : ℕ :=
  2 ^ Uniform713.stopLevel (fun k => dyadicMean Tier2.observations k ω) L

def classifierValue (L : ℕ) (ω : ℕ → Bool) : ℝ :=
  decisions Tier2.observations L ω

theorem measurable_classifierCost (L : ℕ) : Measurable (classifierCost L) :=
  (measurable_of_countable (fun n : ℕ => 2^n)).comp
    (Uniform713.measurable_stopLevel (dyadicMean Tier2.observations)
      (fun _k => measurable_prefixMean Tier2.measurable_observations _) L)

theorem measurable_classifierValue (L : ℕ) : Measurable (classifierValue L) :=
  Uniform713.measurable_decision (dyadicMean Tier2.observations)
    (fun _k => measurable_prefixMean Tier2.measurable_observations _) L

theorem classifier_prefix_ext (L : ℕ) (ω ω' : ℕ → Bool)
    (h : Tier2.tapePrefix (classifierCost L ω) ω = Tier2.tapePrefix (classifierCost L ω) ω') :
    classifierCost L ω' = classifierCost L ω ∧ classifierValue L ω' = classifierValue L ω := by
  let m := fun k => dyadicMean Tier2.observations k ω
  let m' := fun k => dyadicMean Tier2.observations k ω'
  have hm (k : ℕ) (hk : k ≤ Uniform713.stopLevel m L) : m' k = m k :=
    (dyadicMean_prefix_ext _ ω ω' h k (Nat.pow_le_pow_right (by omega : 0 < 2) hk)).symm
  have he : Uniform713.stopLevel m' L = Uniform713.stopLevel m L :=
    firstStop_congr_until _ m m' L hm
  constructor
  · exact congrArg (fun k : ℕ => 2^k) he
  · change firstDecision _ m' L = firstDecision _ m L
    unfold firstDecision
    change (if 1/2 < m' (Uniform713.stopLevel m' L) then (1 : ℝ) else 0) = _
    rw [he,hm _ le_rfl]
    rfl

theorem classifierCost_mono (ω : ℕ → Bool) {k L : ℕ} (hk : k ≤ L) :
    classifierCost k ω ≤ classifierCost L ω :=
  Nat.pow_le_pow_right (by omega : 0 < 2) (Uniform713.stopLevel_mono _ hk)

def callCost (z : ℕ × (ℕ → Bool)) : ℕ := classifierCost z.1 z.2
def callValue (z : ℕ × (ℕ → Bool)) : ℝ := estimator (decisions Tier2.observations) z

theorem measurable_callCost : Measurable callCost :=
  measurable_from_prod_countable_right measurable_classifierCost

theorem measurable_callValue : Measurable callValue :=
  measurable_estimator measurable_classifierValue

theorem call_prefix_ext (l : ℕ) (ω ω' : ℕ → Bool)
    (h : Tier2.tapePrefix (callCost (l,ω)) ω = Tier2.tapePrefix (callCost (l,ω)) ω') :
    callCost (l,ω') = callCost (l,ω) ∧ callValue (l,ω') = callValue (l,ω) := by
  have hf := classifier_prefix_ext l ω ω' h
  refine ⟨hf.1, ?_⟩
  cases l with
  | zero => exact congrArg (fun v => v / levelProb 0) hf.2
  | succ l =>
    have hc := (classifier_prefix_ext l ω ω'
      (prefix_eq_restrict h (classifierCost_mono ω (Nat.le_succ l)))).2
    change (classifierValue (l+1) ω' - classifierValue l ω') / levelProb (l+1) = _
    rw [hf.2,hc]
    rfl

theorem callCost_eq_work (z : ℕ × (ℕ → Bool)) :
    (callCost z : ℝ) = sampled (Uniform713.levelWork Tier2.observations) z := by
  simp [callCost,classifierCost,sampled,Uniform713.levelWork,Uniform713.work,cap]

theorem callCost_pos (z : ℕ × (ℕ → Bool)) : 0 < callCost z := Nat.two_pow_pos _

theorem callCost_le (z : ℕ × (ℕ → Bool)) : callCost z ≤ 2^z.1 :=
  Nat.pow_le_pow_right (by omega : 0 < 2) (Uniform713.stopLevel_le _ _)

end ThresholdHC.Observable713
