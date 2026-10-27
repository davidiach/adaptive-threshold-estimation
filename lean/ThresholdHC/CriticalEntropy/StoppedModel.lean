import Mathlib
import ThresholdHC.Proofs.Tier2.ClassifierProbability

/-!
Observable single-coin procedures with measurable outputs and honest extended
stopping times. The procedure has no coin-parameter argument. Its terminal
output on each exact stopping event is a function of the seed and that prefix.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ThresholdHC.CriticalEntropy

def tapeDrop (n : ℕ) (ω : ℕ → Bool) : ℕ → Bool := fun k => ω (n+k)

theorem measurable_tapeDrop (n : ℕ) : Measurable (tapeDrop n) :=
  Measurable.of_eval (fun k => measurable_pi_apply (n+k))

/-- An observable stopped procedure with an arbitrary measurable output.
Exact stopping and the output on that event are determined by the seed and
the observed prefix. The procedure is not indexed by the Bernoulli parameter. -/
structure StoppedProcedure (R E : Type) [MeasurableSpace R] [MeasurableSpace E] where
  stop : R × (ℕ → Bool) → ℕ∞
  output : R × (ℕ → Bool) → E
  measurable_stop : Measurable stop
  measurable_output : Measurable output
  stopPrefix : (n : ℕ) → Set (R × (Fin n → Bool))
  measurable_stopPrefix : ∀ n, MeasurableSet (stopPrefix n)
  stop_observable : ∀ n z,
    (z.1, Tier2.tapePrefix n z.2) ∈ stopPrefix n ↔ stop z = n
  outputPrefix : (n : ℕ) → R × (Fin n → Bool) → E
  measurable_outputPrefix : ∀ n, Measurable (outputPrefix n)
  output_observable : ∀ (n : ℕ) z, stop z = n →
    output z = outputPrefix n (z.1, Tier2.tapePrefix n z.2)

def stoppedSuffix {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (z : R × (ℕ → Bool)) : ℕ → Bool :=
  tapeDrop (A.stop z).toNat z.2

theorem measurable_stoppedSuffix {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) : Measurable (stoppedSuffix A) := by
  have hd : Measurable (fun z : ℕ × (ℕ → Bool) => tapeDrop z.1 z.2) :=
    measurable_from_prod_countable_right (fun n => measurable_tapeDrop n)
  exact hd.comp (((measurable_of_countable ENat.toNat).comp A.measurable_stop).prodMk
    measurable_snd)

/-- Number of flips, retaining infinite work. -/
def stoppedProcedureWork {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (z : R × (ℕ → Bool)) : ℝ≥0∞ := A.stop z

def expectedStoppedProcedureWork {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) (p : unitInterval) (A : StoppedProcedure R E) : ℝ≥0∞ :=
  ∫⁻ z, stoppedProcedureWork A z ∂ν.prod (Tier2.tapeMeasure p)

theorem measurable_stoppedProcedureWork {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E] (A : StoppedProcedure R E) :
    Measurable (stoppedProcedureWork A) :=
  (measurable_of_countable ENat.toENNReal).comp A.measurable_stop

/-- Record the actual stopping time together with the output. -/
def stoppedWithWork {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) : StoppedProcedure R (ℕ∞ × E) where
  stop := A.stop
  output := fun z => (A.stop z, A.output z)
  measurable_stop := A.measurable_stop
  measurable_output := A.measurable_stop.prodMk A.measurable_output
  stopPrefix := A.stopPrefix
  measurable_stopPrefix := A.measurable_stopPrefix
  stop_observable := A.stop_observable
  outputPrefix := fun n z => ((n : ℕ∞), A.outputPrefix n z)
  measurable_outputPrefix := fun n => measurable_const.prodMk (A.measurable_outputPrefix n)
  output_observable := fun n z hn => Prod.ext hn (A.output_observable n z hn)

end ThresholdHC.CriticalEntropy
