import ThresholdHC.BlindUpper.ClassifierProcedure

noncomputable section

namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy

def cutoffCost (L : ℕ) (z : ℕ × (ℕ → Bool)) : ℕ :=
  if z.1 ≤ L then classifierStop z.1 z.2 else 0

def cutoffValue (L : ℕ) (z : ℕ × (ℕ → Bool)) : ℝ :=
  if z.1 ≤ L then
    (if z.1 = 0 then classifierValue 0 z.2
      else classifierValue z.1 z.2-classifierValue (z.1-1) z.2) / ThresholdHC.pLevel z.1
  else 0

theorem measurable_cutoffCost (L : ℕ) : Measurable (cutoffCost L) := by
  apply measurable_from_prod_countable_right
  intro l
  by_cases h : l ≤ L
  · simpa [cutoffCost,h] using measurable_classifierStop l
  · simpa [cutoffCost,h] using (measurable_const : Measurable (fun _ : ℕ → Bool => (0 : ℕ)))

theorem measurable_cutoffValue (L : ℕ) : Measurable (cutoffValue L) := by
  apply measurable_from_prod_countable_right
  intro l
  by_cases h : l ≤ L
  · by_cases hz : l = 0
    · simpa [cutoffValue,h,hz] using (measurable_classifierValue 0).div_const (ThresholdHC.pLevel l)
    · simpa [cutoffValue,h,hz,Pi.sub_apply] using
        ((measurable_classifierValue l).sub (measurable_classifierValue (l-1))).div_const (ThresholdHC.pLevel l)
  · simpa [cutoffValue,h] using (measurable_const : Measurable (fun _ : ℕ → Bool => (0 : ℝ)))

theorem cutoff_prefix_ext (L l : ℕ) (ω ω' : ℕ → Bool)
    (h : Tier2.tapePrefix (cutoffCost L (l,ω)) ω = Tier2.tapePrefix (cutoffCost L (l,ω)) ω') :
    cutoffCost L (l,ω') = cutoffCost L (l,ω) ∧ cutoffValue L (l,ω') = cutoffValue L (l,ω) := by
  by_cases hl : l ≤ L
  · have hc : cutoffCost L (l,ω) = classifierStop l ω := ite_eq_left hl
    rw [hc] at h
    have hh := h
    have he := classifier_prefix_ext l ω ω' hh
    constructor
    · simpa [cutoffCost,hl] using he.1
    · by_cases hz : l=0
      · subst l
        simp [cutoffValue,hl,he.2]
      · have hm := classifierStop_mono ω (Nat.sub_le l 1)
        have he' := classifier_prefix_ext (l-1) ω ω' (prefix_eq_restrict hh hm)
        simp [cutoffValue,hl,hz,he.2,he'.2]
  · simp [cutoffCost,cutoffValue,hl]

/-- Draw the unbounded geometric level as an independent seed. Levels above L
return zero without flips; accepted levels run the two classifiers on a shared
prefix and stop at the larger classifier's actual stopping count. -/
def cutoffProcedure (L : ℕ) : StoppedProcedure ℕ ℝ :=
  finiteStoppedProcedure (cutoffCost L) (cutoffValue L)
    (measurable_cutoffCost L) (measurable_cutoffValue L) (cutoff_prefix_ext L)

theorem cutoffCost_le (L : ℕ) (z : ℕ × (ℕ → Bool)) : cutoffCost L z ≤ 2^L := by
  by_cases h : z.1 ≤ L
  · rw [cutoffCost,ite_eq_left h]
    exact (classifierStop_le z.1 z.2).trans (Nat.pow_le_pow_right (by omega : 0 < 2) h)
  · simp [cutoffCost,h]

theorem cutoff_zero_level_cost (L : ℕ) (ω : ℕ → Bool) : cutoffCost L (0,ω) = 1 := by
  have h := Tier2.Model.stopLevel_le (fun k => Uniform713.dyadicMean Tier2.observations k ω) 0
  have he : Tier2.Model.stopLevel (fun k => Uniform713.dyadicMean Tier2.observations k ω) 0 = 0 := by omega
  simp [cutoffCost,classifierStop,he]

end ThresholdHC.BlindUpper
