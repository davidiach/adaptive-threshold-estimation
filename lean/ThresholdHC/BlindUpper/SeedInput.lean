import ThresholdHC.BlindUpper.InfiniteArrays
import ThresholdHC.BlindUpper.CutoffBatch

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ProbabilityTheory
open ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open scoped ENNReal

theorem product_swap_last_preserving {X Y Z : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (τ : Measure Z)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure τ] :
    MeasurePreserving (fun z : (X × Y) × Z => ((z.1.1,z.2),z.1.2))
      ((μ.prod ν).prod τ) ((μ.prod τ).prod ν) := by
  have h1 := measurePreserving_prodAssoc μ ν τ
  have h2 := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := ν) (ν := τ))
  have h3 := (measurePreserving_prodAssoc μ τ ν).symm MeasurableEquiv.prodAssoc
  exact h3.comp (h2.comp h1)

/-- A seed contains only independent geometric levels and uniform marks. -/
abbrev BatchSeed := ℕ → ℕ × ℝ

def batchSeedLaw : Measure BatchSeed :=
  Measure.infinitePi (fun _ : ℕ => levelMeasure.prod uniformUnitMeasure)

instance batchSeedLaw_probability : IsProbabilityMeasure batchSeedLaw := by
  unfold batchSeedLaw
  infer_instance

def seededMarkedCalls (z : BatchSeed × (ℕ → ℕ → Bool)) : ℕ → (ℕ × (ℕ → Bool)) × ℝ :=
  fun i => ((z.1 i |>.1,z.2 i),z.1 i |>.2)

theorem measurable_seededMarkedCalls : Measurable seededMarkedCalls := by
  apply Measurable.of_eval
  intro i
  exact (((measurable_pi_apply i).comp measurable_fst).fst.prodMk
    ((measurable_pi_apply i).comp measurable_snd)).prodMk
      ((measurable_pi_apply i).comp measurable_fst).snd

theorem seededMarkedCalls_map (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (batchSeedLaw.prod (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))).map
      seededMarkedCalls = markedSequenceLaw (callMeasure μ q) := by
  let f : ((ℕ × ℝ) × (ℕ → Bool)) → ((ℕ × (ℕ → Bool)) × ℝ) :=
    fun z => ((z.1.1,z.2),z.1.2)
  have hf : Measurable f := (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  have hfm : Measurable (fun z : ℕ → (ℕ × ℝ) × (ℕ → Bool) => fun i => f (z i)) :=
    Measurable.of_eval (fun i => hf.comp (measurable_pi_apply i))
  have he : seededMarkedCalls = (fun z i => f (z i)) ∘ (fun z i => (z.1 i,z.2 i)) := rfl
  rw [he,← Measure.map_map hfm (by fun_prop)]
  unfold batchSeedLaw
  rw [infinitePi_zip,Measure.infinitePi_map_pi _ (fun _ => hf)]
  have h := (product_swap_last_preserving levelMeasure uniformUnitMeasure
    (originalPopulationTapeLaw μ q)).map_eq
  change (Measure.infinitePi (fun _ : ℕ =>
    ((levelMeasure.prod uniformUnitMeasure).prod (originalPopulationTapeLaw μ q)).map f)) = _
  simp_rw [show ((levelMeasure.prod uniformUnitMeasure).prod (originalPopulationTapeLaw μ q)).map f =
    (callMeasure μ q).prod uniformUnitMeasure from h]
  rfl

def threeMarkedStreams {X : Type} (z : ℕ → X × ℝ) : CalibrationState X :=
  ((fun i => z (Nat.pair 0 i),fun i => z (Nat.pair 1 i)),fun i => (z (Nat.pair 2 i)).1)

theorem measurable_threeMarkedStreams {X : Type} [MeasurableSpace X] :
    Measurable (threeMarkedStreams (X := X)) :=
  ((Measurable.of_eval (fun i => measurable_pi_apply (Nat.pair 0 i))).prodMk
    (Measurable.of_eval (fun i => measurable_pi_apply (Nat.pair 1 i)))).prodMk
      (Measurable.of_eval (fun i => (measurable_pi_apply (Nat.pair 2 i)).fst))

theorem threeMarkedStreams_map {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] :
    (markedSequenceLaw ν).map threeMarkedStreams = calibrationLaw ν := by
  let π := markedSequenceLaw ν
  have hp : π.map (fun z i => (z i).1) = Measure.infinitePi (fun _ : ℕ => ν) := by
    rw [show π = Measure.infinitePi (fun _ : ℕ => ν.prod uniformUnitMeasure) from rfl,
      Measure.infinitePi_map_pi _ (fun _ => measurable_fst)]
    simp only [Measure.map_fst_prod,measure_univ,one_smul]
  let g : ((ℕ → X × ℝ) × (ℕ → X × ℝ)) × (ℕ → X × ℝ) → CalibrationState X :=
    fun z => (z.1,fun i => (z.2 i).1)
  have hg : Measurable g := measurable_fst.prodMk
    (Measurable.of_eval (fun i => ((measurable_pi_apply i).comp measurable_snd).fst))
  have ht : Measurable (fun z : ℕ → ℕ → X × ℝ => ((z 0,z 1),z 2)) :=
    ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1)).prodMk (measurable_pi_apply 2)
  change (markedSequenceLaw ν).map
    (g ∘ ((fun z => ((z 0,z 1),z 2)) ∘ splitPairArray)) = _
  rw [← Measure.map_map hg (ht.comp measurable_splitPairArray),
    ← Measure.map_map ht measurable_splitPairArray]
  unfold markedSequenceLaw
  rw [splitPairArray_map,infinitePi_three]
  change ((π.prod π).prod π).map (Prod.map id (fun z i => (z i).1)) = _
  rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop),Measure.map_id,hp]
  rfl

def batchInput : BatchSeed × (ℕ → ℕ → Bool) → CalibrationState (ℕ × (ℕ → Bool)) :=
  threeMarkedStreams ∘ seededMarkedCalls

theorem measurable_batchInput : Measurable batchInput :=
  measurable_threeMarkedStreams.comp measurable_seededMarkedCalls

/-- The actual independent seed/tape law gives exactly the calibrated call law. -/
theorem batchInput_preserving (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    MeasurePreserving batchInput
      (batchSeedLaw.prod (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))
      (calibrationLaw (callMeasure μ q)) := by
  refine ⟨measurable_batchInput,?_⟩
  rw [batchInput,← Measure.map_map measurable_threeMarkedStreams measurable_seededMarkedCalls,
    seededMarkedCalls_map,threeMarkedStreams_map]

end ThresholdHC.BlindUpper
