import ThresholdHC.CriticalEntropy.StoppedModel

/-!
Observable composition on one coin tape. All prefix and legality properties
are pointwise statements, independent of probability laws or termination
assumptions. Completion by false flips is only a canonical representation
of a finite prefix, not an alteration of the experiment.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

def completePrefix (n : ℕ) (w : Fin n → Bool) : ℕ → Bool :=
  fun k => if h : k < n then w ⟨k, h⟩ else false

theorem measurable_completePrefix (n : ℕ) : Measurable (completePrefix n) := by
  apply Measurable.of_eval
  intro k
  by_cases h : k < n
  · simpa only [completePrefix, dite_eq_left h] using (measurable_pi_apply (⟨k,h⟩ : Fin n))
  · simpa only [completePrefix, dite_eq_right h] using
      (measurable_const : Measurable (fun _ : Fin n → Bool => false))

theorem tapePrefix_completePrefix (n : ℕ) (w : Fin n → Bool) :
    Tier2.tapePrefix n (completePrefix n w) = w := by
  funext i
  simp [Tier2.tapePrefix, completePrefix, i.isLt]

theorem prefix_eq_restrict {n k : ℕ} {ω ω' : ℕ → Bool}
    (h : Tier2.tapePrefix n ω = Tier2.tapePrefix n ω') (hk : k ≤ n) :
    Tier2.tapePrefix k ω = Tier2.tapePrefix k ω' := by
  funext i
  exact congrFun h ⟨i.val, lt_of_lt_of_le i.isLt hk⟩

theorem prefix_eq_drop {n k m : ℕ} {ω ω' : ℕ → Bool}
    (h : Tier2.tapePrefix n ω = Tier2.tapePrefix n ω') (hk : k+m ≤ n) :
    Tier2.tapePrefix m (tapeDrop k ω) = Tier2.tapePrefix m (tapeDrop k ω') := by
  funext i
  exact congrFun h ⟨k+i.val, lt_of_lt_of_le (Nat.add_lt_add_left i.isLt k) hk⟩

theorem stopped_prefix_ext {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (r : R) (ω ω' : ℕ → Bool) (n : ℕ)
    (h : Tier2.tapePrefix n ω = Tier2.tapePrefix n ω')
    (hn : A.stop (r, ω) = n) :
    A.stop (r, ω') = n ∧ A.output (r, ω') = A.output (r, ω) := by
  have hh := (A.stop_observable n (r, ω)).mpr hn
  change (r, Tier2.tapePrefix n ω) ∈ A.stopPrefix n at hh
  rw [h] at hh
  have hn' := (A.stop_observable n (r, ω')).mp hh
  refine ⟨hn', ?_⟩
  rw [A.output_observable n (r, ω') hn', A.output_observable n (r, ω) hn, h]

def restartInput {R S E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (z : (R × S) × (ℕ → Bool)) : S × (ℕ → Bool) :=
  (z.1.2, stoppedSuffix A (z.1.1, z.2))

theorem measurable_restartInput {R S E : Type}
    [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E]
    (A : StoppedProcedure R E) : Measurable (restartInput (S := S) A) :=
  measurable_fst.snd.prodMk ((measurable_stoppedSuffix A).comp
    (measurable_fst.fst.prodMk measurable_snd))

def sequentialStop {R S E F : Type}
    [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E] [MeasurableSpace F]
    (A : StoppedProcedure R E) (B : StoppedProcedure S F)
    (z : (R × S) × (ℕ → Bool)) : ℕ∞ :=
  A.stop (z.1.1, z.2) + B.stop (restartInput A z)

def sequentialOutput {R S E F : Type}
    [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E] [MeasurableSpace F]
    (A : StoppedProcedure R E) (B : StoppedProcedure S F)
    (z : (R × S) × (ℕ → Bool)) : E × F :=
  (A.output (z.1.1, z.2), B.output (restartInput A z))

theorem measurable_sequentialStop {R S E F : Type}
    [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E] [MeasurableSpace F]
    (A : StoppedProcedure R E) (B : StoppedProcedure S F) :
    Measurable (sequentialStop A B) :=
  (measurable_of_countable (fun z : ℕ∞ × ℕ∞ => z.1+z.2)).comp
    ((A.measurable_stop.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
      (B.measurable_stop.comp (measurable_restartInput A)))

theorem measurable_sequentialOutput {R S E F : Type}
    [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E] [MeasurableSpace F]
    (A : StoppedProcedure R E) (B : StoppedProcedure S F) :
    Measurable (sequentialOutput A B) :=
  (A.measurable_output.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
    (B.measurable_output.comp (measurable_restartInput A))

theorem sequential_prefix_ext {R S E F : Type}
    [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E] [MeasurableSpace F]
    (A : StoppedProcedure R E) (B : StoppedProcedure S F)
    (r : R) (s : S) (ω ω' : ℕ → Bool) (n : ℕ)
    (h : Tier2.tapePrefix n ω = Tier2.tapePrefix n ω')
    (hn : sequentialStop A B ((r,s),ω) = n) :
    sequentialStop A B ((r,s),ω') = n ∧
      sequentialOutput A B ((r,s),ω') = sequentialOutput A B ((r,s),ω) := by
  have hA : A.stop (r,ω) ≠ ⊤ := by
    intro hh
    simp [sequentialStop, hh] at hn
  obtain ⟨k,hk⟩ := ENat.ne_top_iff_exists.mp hA
  have hB : B.stop (s,stoppedSuffix A (r,ω)) ≠ ⊤ := by
    intro hh
    simp [sequentialStop, restartInput, hh] at hn
  obtain ⟨m,hm⟩ := ENat.ne_top_iff_exists.mp hB
  have hkm : k+m = n := by
    change A.stop (r,ω) + B.stop (s,stoppedSuffix A (r,ω)) = n at hn
    rw [← hk, ← hm, ← Nat.cast_add] at hn
    exact ENat.natCast_inj.mp hn
  have hka : k ≤ n := hkm ▸ Nat.le_add_right k m
  obtain ⟨hk',hoA⟩ := stopped_prefix_ext A r ω ω' k (prefix_eq_restrict h hka) hk.symm
  have hs : Tier2.tapePrefix m (stoppedSuffix A (r,ω)) =
      Tier2.tapePrefix m (stoppedSuffix A (r,ω')) := by
    simp only [stoppedSuffix, ← hk, hk', ENat.toNat_natCast]
    exact prefix_eq_drop h hkm.le
  obtain ⟨hm',hoB⟩ := stopped_prefix_ext B s (stoppedSuffix A (r,ω))
    (stoppedSuffix A (r,ω')) m hs hm.symm
  constructor
  · change A.stop (r,ω') + B.stop (s,stoppedSuffix A (r,ω')) = n
    rw [hk', hm', ← Nat.cast_add, hkm]
  · exact Prod.ext hoA hoB

/-- Run two procedures on successive portions of the same tape. The seeds
are separate coordinates, and stopping at infinity still gives infinite
total work. Legality is established for every tape, before any probability
or finite-expectation assumption is made. -/
def sequentialProcedure {R S E F : Type}
    [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E] [MeasurableSpace F]
    (A : StoppedProcedure R E) (B : StoppedProcedure S F) :
    StoppedProcedure (R × S) (E × F) where
  stop := sequentialStop A B
  output := sequentialOutput A B
  measurable_stop := measurable_sequentialStop A B
  measurable_output := measurable_sequentialOutput A B
  stopPrefix := fun n => {z | sequentialStop A B (z.1, completePrefix n z.2) = n}
  measurable_stopPrefix := fun n =>
    ((measurable_sequentialStop A B).comp
      (measurable_fst.prodMk ((measurable_completePrefix n).comp measurable_snd)))
        (measurableSet_singleton (n : ℕ∞))
  stop_observable := by
    intro n z
    change sequentialStop A B (z.1, completePrefix n (Tier2.tapePrefix n z.2)) = n ↔
      sequentialStop A B z = n
    have h := tapePrefix_completePrefix n (Tier2.tapePrefix n z.2)
    constructor
    · intro hn
      exact (sequential_prefix_ext A B z.1.1 z.1.2 _ z.2 n h hn).1
    · intro hn
      exact (sequential_prefix_ext A B z.1.1 z.1.2 z.2 _ n h.symm hn).1
  outputPrefix := fun n z => sequentialOutput A B (z.1, completePrefix n z.2)
  measurable_outputPrefix := fun n =>
    (measurable_sequentialOutput A B).comp
      (measurable_fst.prodMk ((measurable_completePrefix n).comp measurable_snd))
  output_observable := by
    intro n z hn
    exact (sequential_prefix_ext A B z.1.1 z.1.2 z.2 _ n
      (tapePrefix_completePrefix n (Tier2.tapePrefix n z.2)).symm hn).2.symm

end ThresholdHC.CriticalEntropy
