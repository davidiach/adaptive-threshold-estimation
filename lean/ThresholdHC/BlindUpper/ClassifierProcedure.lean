import ThresholdHC.BlindUpper.FiniteProcedure
import ThresholdHC.Proofs.Tier2.ClassifierModel

noncomputable section

namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Uniform713

theorem firstStop_congr_until (b : ℕ → ℕ → ℝ) (m m' : ℕ → ℝ) (L : ℕ)
    (hm : ∀ k ≤ firstStop b m L, m' k = m k) :
    firstStop b m' L = firstStop b m L := by
  apply (firstStop_eq_iff b m' L _).2
  constructor
  · simpa only [hm _ le_rfl] using firstStop_spec b m L
  · intro k hk
    simpa only [hm k hk.le] using firstStop_min b m L k hk

theorem dyadicMean_prefix_ext (n : ℕ) (ω ω' : ℕ → Bool)
    (h : Tier2.tapePrefix n ω = Tier2.tapePrefix n ω') (k : ℕ) (hk : 2^k ≤ n) :
    dyadicMean Tier2.observations k ω = dyadicMean Tier2.observations k ω' := by
  unfold dyadicMean prefixMean
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg Tier2.bit (congrFun h ⟨i,lt_of_lt_of_le (Finset.mem_range.mp hi) hk⟩)

def classifierStop (L : ℕ) (ω : ℕ → Bool) : ℕ :=
  2 ^ Tier2.Model.stopLevel (fun k => dyadicMean Tier2.observations k ω) L

def classifierValue (L : ℕ) (ω : ℕ → Bool) : ℝ :=
  Tier2.Model.decision (fun k => dyadicMean Tier2.observations k ω) L

theorem measurable_classifierStop (L : ℕ) : Measurable (classifierStop L) :=
  (measurable_of_countable (fun n : ℕ => 2^n)).comp
    (Tier2.Model.measurable_stopLevel (dyadicMean Tier2.observations)
      (fun k => measurable_prefixMean Tier2.measurable_observations _) L)

theorem measurable_classifierValue (L : ℕ) : Measurable (classifierValue L) :=
  Tier2.Model.measurable_decision (dyadicMean Tier2.observations)
    (fun k => measurable_prefixMean Tier2.measurable_observations _) L

theorem classifier_prefix_ext (L : ℕ) (ω ω' : ℕ → Bool)
    (h : Tier2.tapePrefix (classifierStop L ω) ω = Tier2.tapePrefix (classifierStop L ω) ω') :
    classifierStop L ω' = classifierStop L ω ∧ classifierValue L ω' = classifierValue L ω := by
  let m := fun k => dyadicMean Tier2.observations k ω
  let m' := fun k => dyadicMean Tier2.observations k ω'
  have hm (k : ℕ) (hk : k ≤ Tier2.Model.stopLevel m L) : m' k = m k :=
    (dyadicMean_prefix_ext _ ω ω' h k (Nat.pow_le_pow_right (by omega : 0 < 2) hk)).symm
  have he : Tier2.Model.stopLevel m' L = Tier2.Model.stopLevel m L :=
    firstStop_congr_until _ m m' L hm
  constructor
  · exact congrArg (fun k : ℕ => 2^k) he
  · change firstDecision _ m' L = firstDecision _ m L
    unfold firstDecision
    change (if 1/2 < m' (Tier2.Model.stopLevel m' L) then (1 : ℝ) else 0) = _
    rw [he,hm _ le_rfl]
    rfl

def classifierProcedure (L : ℕ) : StoppedProcedure Unit ℝ :=
  finiteStoppedProcedure (fun z => classifierStop L z.2) (fun z => classifierValue L z.2)
    ((measurable_classifierStop L).comp measurable_snd)
    ((measurable_classifierValue L).comp measurable_snd)
    (fun _ ω ω' h => classifier_prefix_ext L ω ω' h)

theorem classifierStop_pos (L : ℕ) (ω : ℕ → Bool) : 0 < classifierStop L ω :=
  Nat.two_pow_pos _

theorem classifierStop_le (L : ℕ) (ω : ℕ → Bool) : classifierStop L ω ≤ 2^L :=
  Nat.pow_le_pow_right (by omega : 0 < 2) (Tier2.Model.stopLevel_le _ L)

theorem classifierStop_mono (ω : ℕ → Bool) {k L : ℕ} (hk : k ≤ L) :
    classifierStop k ω ≤ classifierStop L ω :=
  Nat.pow_le_pow_right (by omega : 0 < 2) (Tier2.Model.stopLevel_mono _ hk)

end ThresholdHC.BlindUpper
