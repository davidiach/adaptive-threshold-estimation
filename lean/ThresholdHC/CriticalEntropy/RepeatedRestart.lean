import ThresholdHC.CriticalEntropy.RepeatedModel
import ThresholdHC.CriticalEntropy.RestartPair

/-!
The actual repeated procedure has an iid output law and exactly n times the
single-run expected work, at each fixed Bernoulli parameter where that work
is finite. The algorithm has no parameter argument and draws no new coin.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem fin_seed_split_map {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.pi (fun _ : Fin (n+1) => ν)).map (fun r => (r 0, Fin.tail r)) =
      ν.prod (Measure.pi (fun _ : Fin n => ν)) := by
  simpa [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.tail] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) 0).map_eq

theorem reseed_expected_work {R S E : Type}
    [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E]
    (ν : Measure S) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R E) (f : S → R) (hf : Measurable f) :
    expectedStoppedProcedureWork ν p (reseedProcedure A f hf) =
      expectedStoppedProcedureWork (ν.map f) p A := by
  unfold expectedStoppedProcedureWork
  rw [← Measure.map_id (μ := Tier2.tapeMeasure p),
    Measure.map_prod_map ν (Tier2.tapeMeasure p) hf measurable_id,
    lintegral_map (measurable_stoppedProcedureWork A) (hf.prodMap measurable_id),
    Measure.map_id]
  rfl

theorem repeated_expected_work {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R E) (hfinite : expectedStoppedProcedureWork ν p A ≠ ∞)
    (n : ℕ) :
    expectedStoppedProcedureWork (Measure.pi (fun _ : Fin n => ν)) p (repeatedProcedure A n) =
      (n : ℝ≥0∞) * expectedStoppedProcedureWork ν p A := by
  induction n with
  | zero => simp [repeatedProcedure, emptyProcedure, expectedStoppedProcedureWork,
      stoppedProcedureWork]
  | succ n ih =>
    change expectedStoppedProcedureWork (Measure.pi (fun _ : Fin (n+1) => ν)) p
      (reseedProcedure (sequentialProcedure A (repeatedProcedure A n))
        (fun r : Fin (n+1) → R => (r 0, Fin.tail r))
        ((measurable_pi_apply 0).prodMk
          (Measurable.of_eval (fun i => measurable_pi_apply i.succ)))) = _
    rw [reseed_expected_work, fin_seed_split_map,
      sequential_expected_work ν (Measure.pi (fun _ : Fin n => ν)) p A
        (repeatedProcedure A n) hfinite, ih]
    simp [Nat.cast_add, add_mul, add_comm]

theorem reseed_output_map {R S E : Type}
    [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E]
    (ν : Measure S) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R E) (f : S → R) (hf : Measurable f) :
    (ν.prod (Tier2.tapeMeasure p)).map (reseedProcedure A f hf).output =
      ((ν.map f).prod (Tier2.tapeMeasure p)).map A.output := by
  rw [← Measure.map_id (μ := Tier2.tapeMeasure p),
    Measure.map_prod_map ν (Tier2.tapeMeasure p) hf measurable_id,
    Measure.map_map A.measurable_output (hf.prodMap measurable_id), Measure.map_id]
  rfl

theorem fin_product_cons_map {E : Type} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) :
    (μ.prod (Measure.pi (fun _ : Fin n => μ))).map
        (fun z => (Fin.cons z.1 z.2 : Fin (n+1) → E)) =
      Measure.pi (fun _ : Fin (n+1) => μ) := by
  simpa [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm.map_eq

theorem repeated_output_map {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : StoppedProcedure R E) (hfinite : expectedStoppedProcedureWork ν p A ≠ ∞)
    (n : ℕ) :
    ((Measure.pi (fun _ : Fin n => ν)).prod (Tier2.tapeMeasure p)).map
        (repeatedProcedure A n).output =
      Measure.pi (fun _ : Fin n => (ν.prod (Tier2.tapeMeasure p)).map A.output) := by
  induction n with
  | zero =>
    apply (Measure.pi_eq (fun s hs => ?_)).symm
    have he : Set.pi Set.univ s = Set.univ := by ext x; simp
    rw [he]
    simp
  | succ n ih =>
    let C : StoppedProcedure (Fin (n+1) → R) (E × (Fin n → E)) :=
      reseedProcedure (sequentialProcedure A (repeatedProcedure A n))
        (fun r : Fin (n+1) → R => (r 0, Fin.tail r))
        ((measurable_pi_apply 0).prodMk
          (Measurable.of_eval (fun i => measurable_pi_apply i.succ)))
    change ((Measure.pi (fun _ : Fin (n+1) => ν)).prod (Tier2.tapeMeasure p)).map
      ((fun z : E × (Fin n → E) => (Fin.cons z.1 z.2 : Fin (n+1) → E)) ∘ C.output) = _
    rw [← Measure.map_map (measurable_finCons n) C.measurable_output]
    unfold C
    rw [reseed_output_map, fin_seed_split_map,
      sequential_output_map ν (Measure.pi (fun _ : Fin n => ν)) p A
        (repeatedProcedure A n) hfinite, ih, fin_product_cons_map]

end ThresholdHC.CriticalEntropy
