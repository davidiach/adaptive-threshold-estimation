import ThresholdHC.CriticalEntropy.SequentialModel

noncomputable section

namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy

/-- Build a legal procedure from a finite stopping count and a prefix-invariant
output. The prefix condition is pointwise, independent of any coin law. -/
def finiteStoppedProcedure {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (cost : R × (ℕ → Bool) → ℕ) (value : R × (ℕ → Bool) → E)
    (hc : Measurable cost) (hv : Measurable value)
    (hext : ∀ (r : R) (ω ω' : ℕ → Bool),
      Tier2.tapePrefix (cost (r,ω)) ω = Tier2.tapePrefix (cost (r,ω)) ω' →
      cost (r,ω') = cost (r,ω) ∧ value (r,ω') = value (r,ω)) : StoppedProcedure R E where
  stop := fun z => (cost z : ℕ∞)
  output := value
  measurable_stop := (measurable_of_countable (fun n : ℕ => (n : ℕ∞))).comp hc
  measurable_output := hv
  stopPrefix := fun n => {z | cost (z.1,completePrefix n z.2) = n}
  measurable_stopPrefix := fun n =>
    measurableSet_eq_fun (hc.comp (measurable_fst.prodMk ((measurable_completePrefix n).comp measurable_snd)))
      measurable_const
  stop_observable := by
    intro n z
    change cost (z.1,completePrefix n (Tier2.tapePrefix n z.2)) = n ↔ (cost z : ℕ∞) = n
    constructor
    · intro h
      have he := hext z.1 (completePrefix n (Tier2.tapePrefix n z.2)) z.2 (by
        rw [h]; exact tapePrefix_completePrefix n _)
      exact_mod_cast he.1.trans h
    · intro h
      have h' : cost z = n := by exact_mod_cast h
      exact (hext z.1 z.2 (completePrefix n (Tier2.tapePrefix n z.2)) (by
        rw [h']; exact (tapePrefix_completePrefix n _).symm)).1.trans h'
  outputPrefix := fun n z => value (z.1,completePrefix n z.2)
  measurable_outputPrefix := fun n =>
    hv.comp (measurable_fst.prodMk ((measurable_completePrefix n).comp measurable_snd))
  output_observable := by
    intro n z h
    have h' : cost z = n := by exact_mod_cast h
    exact (hext z.1 z.2 (completePrefix n (Tier2.tapePrefix n z.2)) (by
      rw [h']; exact (tapePrefix_completePrefix n _).symm)).2.symm

end ThresholdHC.BlindUpper
