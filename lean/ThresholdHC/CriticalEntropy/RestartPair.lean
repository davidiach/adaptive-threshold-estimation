import ThresholdHC.CriticalEntropy.StoppedTape
import ThresholdHC.CriticalEntropy.SequentialModel

/-!
Successive runs with independent seeds use one unchanged Bernoulli parameter.
Their joint output/work law and additive expected work are derived from the
unused-suffix theorem. The second run may have infinite expected work.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem prod_swap_middle {R S T : Type}
    [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure R) (ν : Measure S) (κ : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure κ] :
    ((μ.prod ν).prod κ).map (fun z => ((z.1.1, z.2), z.1.2)) =
      (μ.prod κ).prod ν := by
  have h₁ := measurePreserving_prodAssoc μ ν κ
  have h₂ := (MeasurePreserving.id μ).prod
    (Measure.measurePreserving_swap (μ := ν) (ν := κ))
  have h₃ := (measurePreserving_prodAssoc μ κ ν).symm
  exact (h₃.comp (h₂.comp h₁)).map_eq

theorem seeded_stopped_suffix_map {R S E : Type}
    [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E]
    (ν : Measure R) (η : Measure S) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (p : unitInterval) (A : StoppedProcedure R E)
    (hfinite : expectedStoppedProcedureWork ν p A ≠ ∞) :
    ((ν.prod η).prod (Tier2.tapeMeasure p)).map
        (fun z => (A.output (z.1.1, z.2), (z.1.2, stoppedSuffix A (z.1.1, z.2)))) =
      ((ν.prod (Tier2.tapeMeasure p)).map A.output).prod (η.prod (Tier2.tapeMeasure p)) := by
  let Q := Tier2.tapeMeasure p
  let O := (ν.prod Q).map A.output
  have : IsProbabilityMeasure O := inferInstance
  have h₁ : MeasurePreserving (fun z : (R × S) × (ℕ → Bool) => ((z.1.1, z.2), z.1.2))
      ((ν.prod η).prod Q) ((ν.prod Q).prod η) :=
    ⟨by fun_prop, prod_swap_middle ν η Q⟩
  have hA : MeasurePreserving (fun z => (A.output z, stoppedSuffix A z))
      (ν.prod Q) (O.prod Q) :=
    ⟨A.measurable_output.prodMk (measurable_stoppedSuffix A),
      stopped_output_suffix_map ν p A (stopped_procedure_terminates ν p A hfinite)⟩
  have h₂ := hA.prod (MeasurePreserving.id η)
  have h₃ : MeasurePreserving (fun z : (E × (ℕ → Bool)) × S => ((z.1.1, z.2), z.1.2))
      ((O.prod Q).prod η) ((O.prod η).prod Q) :=
    ⟨by fun_prop, prod_swap_middle O Q η⟩
  have h₄ := measurePreserving_prodAssoc O η Q
  exact (h₄.comp (h₃.comp (h₂.comp h₁))).map_eq

/-- Independent seeds, successive unused flips, one fixed Bernoulli parameter.
The second procedure need not have finite expected work for this law identity. -/
theorem two_run_marked_map {R S E F : Type}
    [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E] [MeasurableSpace F]
    (ν : Measure R) (η : Measure S) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (p : unitInterval) (A : StoppedProcedure R E) (B : StoppedProcedure S F)
    (hfinite : expectedStoppedProcedureWork ν p A ≠ ∞) :
    ((ν.prod η).prod (Tier2.tapeMeasure p)).map
        (fun z => ((A.stop (z.1.1, z.2), A.output (z.1.1, z.2)),
          (B.stop (z.1.2, stoppedSuffix A (z.1.1, z.2)),
            B.output (z.1.2, stoppedSuffix A (z.1.1, z.2))))) =
      ((ν.prod (Tier2.tapeMeasure p)).map (fun z => (A.stop z, A.output z))).prod
        ((η.prod (Tier2.tapeMeasure p)).map (fun z => (B.stop z, B.output z))) := by
  have h₁ : MeasurePreserving
      (fun z : (R × S) × (ℕ → Bool) =>
        ((A.stop (z.1.1, z.2), A.output (z.1.1, z.2)),
          (z.1.2, stoppedSuffix A (z.1.1, z.2))))
      ((ν.prod η).prod (Tier2.tapeMeasure p))
      (((ν.prod (Tier2.tapeMeasure p)).map (fun z => (A.stop z, A.output z))).prod
        (η.prod (Tier2.tapeMeasure p))) :=
    ⟨((A.measurable_stop.prodMk A.measurable_output).comp
        (measurable_fst.fst.prodMk measurable_snd)).prodMk
      (measurable_fst.snd.prodMk ((measurable_stoppedSuffix A).comp
        (measurable_fst.fst.prodMk measurable_snd))),
      seeded_stopped_suffix_map ν η p (stoppedWithWork A) hfinite⟩
  have hB : MeasurePreserving (fun z => (B.stop z, B.output z))
      (η.prod (Tier2.tapeMeasure p))
      ((η.prod (Tier2.tapeMeasure p)).map (fun z => (B.stop z, B.output z))) :=
    ⟨B.measurable_stop.prodMk B.measurable_output, rfl⟩
  exact ((MeasurePreserving.id _).prod hB |>.comp h₁).map_eq

theorem two_run_expected_work {R S E F : Type}
    [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E] [MeasurableSpace F]
    (ν : Measure R) (η : Measure S) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (p : unitInterval) (A : StoppedProcedure R E) (B : StoppedProcedure S F)
    (hfinite : expectedStoppedProcedureWork ν p A ≠ ∞) :
    (∫⁻ z, stoppedProcedureWork A (z.1.1, z.2) +
      stoppedProcedureWork B (z.1.2, stoppedSuffix A (z.1.1, z.2))
        ∂(ν.prod η).prod (Tier2.tapeMeasure p)) =
      expectedStoppedProcedureWork ν p A + expectedStoppedProcedureWork η p B := by
  let f := fun z : (R × S) × (ℕ → Bool) =>
    ((A.stop (z.1.1, z.2), A.output (z.1.1, z.2)),
      (B.stop (z.1.2, stoppedSuffix A (z.1.1, z.2)),
        B.output (z.1.2, stoppedSuffix A (z.1.1, z.2))))
  have hf : Measurable f :=
    ((A.measurable_stop.prodMk A.measurable_output).comp
      (measurable_fst.fst.prodMk measurable_snd)).prodMk
      ((B.measurable_stop.prodMk B.measurable_output).comp
        (measurable_fst.snd.prodMk ((measurable_stoppedSuffix A).comp
          (measurable_fst.fst.prodMk measurable_snd))))
  let g := fun z : (ℕ∞ × E) × (ℕ∞ × F) =>
    (z.1.1 : ℝ≥0∞) + (z.2.1 : ℝ≥0∞)
  have h₁ : Measurable (fun z : (ℕ∞ × E) × (ℕ∞ × F) => (z.1.1 : ℝ≥0∞)) :=
    (measurable_of_countable ENat.toENNReal).comp measurable_fst.fst
  have h₂ : Measurable (fun z : (ℕ∞ × E) × (ℕ∞ × F) => (z.2.1 : ℝ≥0∞)) :=
    (measurable_of_countable ENat.toENNReal).comp measurable_snd.fst
  have hg : Measurable g := h₁.add h₂
  change (∫⁻ z, g (f z) ∂(ν.prod η).prod (Tier2.tapeMeasure p)) = _
  rw [← lintegral_map hg hf]
  change (∫⁻ z, g z ∂((ν.prod η).prod (Tier2.tapeMeasure p)).map _) = _
  rw [two_run_marked_map ν η p A B hfinite]
  change (∫⁻ z : (ℕ∞ × E) × (ℕ∞ × F),
    (z.1.1 : ℝ≥0∞) + (z.2.1 : ℝ≥0∞) ∂_) = _
  rw [lintegral_add_left h₁, lintegral_prod _ h₁.aemeasurable,
    lintegral_prod _ h₂.aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]
  have he : Measurable (fun z : ℕ∞ × E => (z.1 : ℝ≥0∞)) :=
    (measurable_of_countable ENat.toENNReal).comp measurable_fst
  have hk : Measurable (fun z : ℕ∞ × F => (z.1 : ℝ≥0∞)) :=
    (measurable_of_countable ENat.toENNReal).comp measurable_fst
  rw [lintegral_map he
      (A.measurable_stop.prodMk A.measurable_output),
    lintegral_map hk
      (B.measurable_stop.prodMk B.measurable_output)]
  rfl

theorem sequential_expected_work {R S E F : Type}
    [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E] [MeasurableSpace F]
    (ν : Measure R) (η : Measure S) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (p : unitInterval) (A : StoppedProcedure R E) (B : StoppedProcedure S F)
    (hfinite : expectedStoppedProcedureWork ν p A ≠ ∞) :
    expectedStoppedProcedureWork (ν.prod η) p (sequentialProcedure A B) =
      expectedStoppedProcedureWork ν p A + expectedStoppedProcedureWork η p B := by
  simpa only [expectedStoppedProcedureWork, stoppedProcedureWork,
    sequentialProcedure, sequentialStop, restartInput, ENat.toENNReal_add] using
    two_run_expected_work ν η p A B hfinite

theorem sequential_output_map {R S E F : Type}
    [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E] [MeasurableSpace F]
    (ν : Measure R) (η : Measure S) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (p : unitInterval) (A : StoppedProcedure R E) (B : StoppedProcedure S F)
    (hfinite : expectedStoppedProcedureWork ν p A ≠ ∞) :
    ((ν.prod η).prod (Tier2.tapeMeasure p)).map (sequentialProcedure A B).output =
      ((ν.prod (Tier2.tapeMeasure p)).map A.output).prod
        ((η.prod (Tier2.tapeMeasure p)).map B.output) := by
  have h₁ : MeasurePreserving
      (fun z : (R × S) × (ℕ → Bool) => (A.output (z.1.1,z.2), restartInput A z))
      ((ν.prod η).prod (Tier2.tapeMeasure p))
      (((ν.prod (Tier2.tapeMeasure p)).map A.output).prod (η.prod (Tier2.tapeMeasure p))) :=
    ⟨(A.measurable_output.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
      (measurable_restartInput A), seeded_stopped_suffix_map ν η p A hfinite⟩
  have hB : MeasurePreserving B.output (η.prod (Tier2.tapeMeasure p))
      ((η.prod (Tier2.tapeMeasure p)).map B.output) := ⟨B.measurable_output, rfl⟩
  exact ((MeasurePreserving.id _).prod hB |>.comp h₁).map_eq

end ThresholdHC.CriticalEntropy
