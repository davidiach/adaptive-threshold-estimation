import ThresholdHC.Confidence.Controller
import ThresholdHC.BlindUpper.BatchRealization

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ThresholdHC.Confidence
open ThresholdHC.Tier6 ThresholdHC.BlindUpper ThresholdHC.ObservableSimulation
open ThresholdHC.CriticalEntropy

instance originalSimulation_probability {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) :
    IsProbabilityMeasure (originalSimulationLaw μ A q) := by
  letI := A.probability
  unfold originalSimulationLaw
  infer_instance

def repeatInputs (z : RepeatSeed × (ℕ → ℕ → Bool)) : ℕ → BatchSeed × (ℕ → ℕ → Bool) :=
  fun i => (z.1 i, fun j => z.2 (Nat.pair i j))

theorem measurable_repeatInputs : Measurable repeatInputs := by
  apply Measurable.of_eval
  intro i
  exact ((measurable_pi_apply i).comp measurable_fst).prodMk
    (Measurable.of_eval (fun j => (measurable_pi_apply (Nat.pair i j)).comp measurable_snd))

theorem repeatInputs_preserving (m L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    MeasurePreserving repeatInputs (originalSimulationLaw μ (repeatEstimator m L) q)
      (Measure.infinitePi (fun _ : ℕ => originalSimulationLaw μ (batchEstimator L) q)) := by
  refine ⟨measurable_repeatInputs, ?_⟩
  let ν := originalPopulationTapeLaw μ q
  have he : repeatInputs =
      (fun z : RepeatSeed × (ℕ → ℕ → ℕ → Bool) => fun i => (z.1 i,z.2 i)) ∘
        Prod.map id splitPairArray := rfl
  change ((Measure.infinitePi (fun _ : ℕ => batchSeedLaw)).prod
    (Measure.infinitePi (fun _ : ℕ => ν))).map repeatInputs = _
  rw [he,← Measure.map_map (by fun_prop) (measurable_id.prodMap measurable_splitPairArray),
    ← Measure.map_prod_map _ _ measurable_id measurable_splitPairArray,
    Measure.map_id,splitPairArray_map,infinitePi_zip]
  rfl

theorem repeatInput_preserving (m L i : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    MeasurePreserving (fun z => repeatInputs z i)
      (originalSimulationLaw μ (repeatEstimator m L) q) (originalSimulationLaw μ (batchEstimator L) q) := by
  have hp : IsProbabilityMeasure (originalSimulationLaw μ (batchEstimator L) q) := by
    change IsProbabilityMeasure (batchSeedLaw.prod _)
    infer_instance
  have hi : MeasurePreserving (fun x : ℕ → BatchSeed × (ℕ → ℕ → Bool) => x i)
      (Measure.infinitePi (fun _ : ℕ => originalSimulationLaw μ (batchEstimator L) q))
      (originalSimulationLaw μ (batchEstimator L) q) :=
    ⟨measurable_pi_apply i,Measure.infinitePi_map_eval _ i⟩
  exact hi.comp (repeatInputs_preserving m L μ q)

def calibrationInputs (z : RepeatSeed × (ℕ → ℕ → Bool)) :=
  fun i : ℕ => batchInput (repeatInputs z i)

theorem measurable_calibrationInputs : Measurable calibrationInputs := by
  apply Measurable.of_eval
  intro i
  exact measurable_batchInput.comp ((measurable_pi_apply i).comp measurable_repeatInputs)

theorem calibrationInputs_preserving (m L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    MeasurePreserving calibrationInputs (originalSimulationLaw μ (repeatEstimator m L) q)
      (Measure.infinitePi (fun _ : ℕ => calibrationLaw (callMeasure μ q))) := by
  refine ⟨measurable_calibrationInputs, ?_⟩
  have hm : Measurable (fun x : ℕ → BatchSeed × (ℕ → ℕ → Bool) => fun i => batchInput (x i)) :=
    Measurable.of_eval (fun i => measurable_batchInput.comp (measurable_pi_apply i))
  change (originalSimulationLaw μ (repeatEstimator m L) q).map
    ((fun x i => batchInput (x i)) ∘ repeatInputs) = _
  rw [← Measure.map_map hm measurable_repeatInputs,(repeatInputs_preserving m L μ q).map_eq,
    Measure.infinitePi_map_pi _ (fun _ => measurable_batchInput)]
  have hbatch : (originalSimulationLaw μ (batchEstimator L) q).map batchInput =
      calibrationLaw (callMeasure μ q) := (batchInput_preserving μ q).map_eq
  simp only [hbatch]

end ThresholdHC.Confidence
