import ThresholdHC.TypedConfidence.ParameterWork

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.TypedConfidence
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.CriticalEntropy
open ThresholdHC.ConfidenceTransfer

local instance : MeasurableSpace (Option Bool) := ⊤
local instance : MeasurableSingletonClass (Option Bool) := ⟨fun _ => trivial⟩

/-- The capped local observation law includes the auxiliary independent tapes. -/
def parameterCappedLaw {m : ℕ} (κ : Fin m → Measure unitInterval)
    (τ : Measure unitInterval) (pol : List Bool → Option (Fin m)) (n : ℕ) (i : Fin m) :=
  ((Measure.pi (fun j => parameterTapeLaw (κ j))).prod (parameterTapeLaw τ)).map
    (cappedTranscript (localSimulationProcedure i n pol) n)

theorem parameter_local_affinity {m : ℕ}
    (κ : Fin m → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (τ υ : Measure unitInterval) [IsProbabilityMeasure τ] [IsProbabilityMeasure υ]
    (pol : List Bool → Option (Fin m)) (n : ℕ) (i : Fin m) :
    (hellingerAffinity (parameterCappedLaw κ τ pol n i) (parameterCappedLaw κ υ pol n i)).toReal ≤
      (hellingerAffinity (parameterWordLaw (Function.update κ i τ) pol n)
        (parameterWordLaw (Function.update κ i υ) pol n)).toReal := by
  have h := cappedOutput_affinity (localSimulationProcedure i n pol) n
    (localSimulationProcedure_capped i n pol)
    ((Measure.pi (fun j => parameterTapeLaw (κ j))).prod (parameterTapeLaw τ))
    ((Measure.pi (fun j => parameterTapeLaw (κ j))).prod (parameterTapeLaw υ))
  rw [parameter_local_word_law,parameter_local_word_law] at h
  exact ENNReal.toReal_mono
    (ne_top_of_le_ne_top (by simp) (hellingerAffinity_probability_le_one _ _)) h

/-- Uniform local Hellinger loss charged to reference work controls the full
finite adaptive experiment, allowing a different parameter law at every label. -/
theorem finite_parameter_reference_kl {m n : ℕ}
    (κ τ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ i, IsProbabilityMeasure (τ i)]
    (pol : List Bool → Option (Fin m)) (K : ℝ) (hK : 0 ≤ K)
    (hbound : let ref := fun i => quarterMix (κ i) (τ i)
      ∀ i : Fin m,
        1-(hellingerAffinity (parameterCappedLaw ref (κ i) pol n i)
          (parameterCappedLaw ref (τ i) pol n i)).toReal ≤
        K*(parameterLocalWork ref pol n i).toReal) :
    let ref := fun i => quarterMix (κ i) (τ i)
    let alt := fun i => quarterMix (τ i) (κ i)
    klDiv (parameterWordLaw ref pol n) (parameterWordLaw alt pol n) ≤
      ENNReal.ofReal ((8/3)*K*(parameterExpectedWork ref pol n).toReal) := by
  classical
  let ref := fun i => quarterMix (κ i) (τ i)
  let alt := fun i => quarterMix (τ i) (κ i)
  let H (i : Fin m) (υ : Measure unitInterval) := parameterWordLaw (Function.update ref i υ) pol n
  have step (i : Fin m) : klDiv (H i (ref i)) (H i (alt i)) ≤
      ENNReal.ofReal ((8/3)*K*(parameterLocalWork ref pol n i).toReal) := by
    dsimp only [H,ref,alt]
    rw [parameter_one_slot_quarter,parameter_one_slot_quarter]
    apply (quarter_smoothing _ _).trans
    apply ENNReal.ofReal_le_ofReal
    have h := (sub_le_sub_left (parameter_local_affinity ref (κ i) (τ i) pol n i) 1).trans (hbound i)
    exact (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 8/3)).trans_eq (by ring)
  change klDiv (parameterWordLaw ref pol n) (parameterWordLaw alt pol n) ≤ _
  rw [quarter_parameter_hybrid_kl]
  calc
    _ ≤ ∑ i : Fin m, ENNReal.ofReal ((8/3)*K*(parameterLocalWork ref pol n i).toReal) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [H,Function.update_eq_self] using step i
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),← Finset.mul_sum,
        parameter_total_work_real]

end ThresholdHC.TypedConfidence
