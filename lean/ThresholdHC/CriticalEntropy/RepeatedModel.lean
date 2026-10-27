import ThresholdHC.CriticalEntropy.SequentialModel

/-!
Finite repetition on successive blocks of one coin tape. The seed and output
vectors have the same fixed length. Observable legality follows from the
pointwise sequential construction, without any law or moment assumption.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

def reseedProcedure {R S E : Type}
    [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E]
    (A : StoppedProcedure R E) (f : S → R) (hf : Measurable f) :
    StoppedProcedure S E where
  stop := fun z => A.stop (f z.1, z.2)
  output := fun z => A.output (f z.1, z.2)
  measurable_stop := A.measurable_stop.comp (hf.prodMap measurable_id)
  measurable_output := A.measurable_output.comp (hf.prodMap measurable_id)
  stopPrefix := fun n => Prod.map f id ⁻¹' A.stopPrefix n
  measurable_stopPrefix := fun n => (hf.prodMap measurable_id) (A.measurable_stopPrefix n)
  stop_observable := fun n z => A.stop_observable n (f z.1,z.2)
  outputPrefix := fun n z => A.outputPrefix n (f z.1,z.2)
  measurable_outputPrefix := fun n => (A.measurable_outputPrefix n).comp (hf.prodMap measurable_id)
  output_observable := fun n z hn => A.output_observable n (f z.1,z.2) hn

def postprocessProcedure {R E F : Type}
    [MeasurableSpace R] [MeasurableSpace E] [MeasurableSpace F]
    (A : StoppedProcedure R E) (f : E → F) (hf : Measurable f) :
    StoppedProcedure R F where
  stop := A.stop
  output := f ∘ A.output
  measurable_stop := A.measurable_stop
  measurable_output := hf.comp A.measurable_output
  stopPrefix := A.stopPrefix
  measurable_stopPrefix := A.measurable_stopPrefix
  stop_observable := A.stop_observable
  outputPrefix := fun n => f ∘ A.outputPrefix n
  measurable_outputPrefix := fun n => hf.comp (A.measurable_outputPrefix n)
  output_observable := fun n z hn => congrArg f (A.output_observable n z hn)

def emptyProcedure (R E : Type) [MeasurableSpace R] [MeasurableSpace E] :
    StoppedProcedure (Fin 0 → R) (Fin 0 → E) where
  stop := fun _ => 0
  output := fun _ => Fin.elim0
  measurable_stop := measurable_const
  measurable_output := measurable_const
  stopPrefix := fun n => if n=0 then Set.univ else ∅
  measurable_stopPrefix := fun n => by split_ifs <;> simp
  stop_observable := by intro n z; simp [eq_comm]
  outputPrefix := fun _ _ => Fin.elim0
  measurable_outputPrefix := fun _ => measurable_const
  output_observable := fun _ _ _ => rfl

theorem measurable_finCons {E : Type} [MeasurableSpace E] (n : ℕ) :
    Measurable (fun z : E × (Fin n → E) => (Fin.cons z.1 z.2 : Fin (n+1) → E)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using (measurable_fst : Measurable (Prod.fst : E × (Fin n → E) → E))
  · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply j).comp
      (measurable_snd : Measurable (Prod.snd : E × (Fin n → E) → (Fin n → E)))

def repeatedProcedure {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) : (n : ℕ) → StoppedProcedure (Fin n → R) (Fin n → E)
  | 0 => emptyProcedure R E
  | n+1 => postprocessProcedure
      (reseedProcedure (sequentialProcedure A (repeatedProcedure A n))
        (fun r : Fin (n+1) → R => (r 0, Fin.tail r))
        ((measurable_pi_apply 0).prodMk
          (Measurable.of_eval (fun i => measurable_pi_apply i.succ))))
      (fun z => Fin.cons z.1 z.2) (measurable_finCons n)

end ThresholdHC.CriticalEntropy
