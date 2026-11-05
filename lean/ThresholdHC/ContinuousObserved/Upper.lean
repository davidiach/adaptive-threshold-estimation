import ThresholdHC.ContinuousObserved.Transfer
import ThresholdHC.BlindUpper.Full
import ThresholdHC.Confidence.Full

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservedState
open ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

def rmsStateEstimator (B : ℝ) : StateEstimator (BatchSeed × (ℕ → unitInterval)) :=
  sampledStateEstimator (budgetEstimator B)

/-- One observed-state family works for every gap law and deterministic
sign-cell model, without access to that law or to its gap map. -/
theorem observed_rms_upper (B : ℝ) (hB : 1 ≤ B) {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (D : QueryDesign N) (s : Fin N → Bool)
    (hl : volume.map D.gap = μ)
    (P : Measure ((BatchSeed × (ℕ → unitInterval)) × ProcessTape)) [IsProbabilityMeasure P]
    (hreal : RealizesQueryPrefixes D (rmsStateEstimator B) s P) :
    (∫⁻ z, totalProcessWork z.2 ∂P) ≤ ENNReal.ofReal B ∧
      rootMeanRisk P (rmsStateEstimator B).output (stateTarget D.cell s) ≤
        ENNReal.ofReal (512 * modulus μ (1 / Real.sqrt B)) := by
  dsimp only [rmsStateEstimator] at hreal ⊢
  constructor
  · rw [sampled_expectedWork μ D s hl (budgetEstimator B) P hreal]
    exact budgetEstimator_uniformBudget B μ (conditionalSign μ D s)
  · rw [sampled_rootMeanRisk μ D s hl (budgetEstimator B) P hreal]
    exact (le_iSup (fun q : SignLaw => rootMeanRisk (experimentLaw μ (budgetEstimator B) q)
      (populationOutput (budgetEstimator B)) (signMean μ q.val)) (conditionalSign μ D s)).trans
      (budgetEstimator_maximalRMSRisk B hB μ)

/-- The confidence family is selected before the gap law, sign-cell design
and deterministic signs, and charges the actual number of inner observations. -/
theorem observed_confidence_upper :
    ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → ℝ → StateEstimator R),
      ∀ B δ : ℝ, 1 ≤ B → 0 < δ → δ ≤ 1 / 4 →
        ∀ (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (D : QueryDesign N) (s : Fin N → Bool),
          volume.map D.gap = μ →
          ∀ (P : Measure (R × ProcessTape)) [IsProbabilityMeasure P],
            RealizesQueryPrefixes D (rule B δ) s P →
            (∫⁻ z, totalProcessWork z.2 ∂P) ≤ ENNReal.ofReal B ∧
              P {z | 8192 * modulus μ (ThresholdHC.Confidence.confidenceScale B δ) <
                |(rule B δ).output z - stateTarget D.cell s|} ≤ ENNReal.ofReal δ := by
  obtain ⟨R,mR,rule,hrule⟩ := ThresholdHC.Confidence.confidence_upper
  refine ⟨R × (ℕ → unitInterval),inferInstance,fun B δ => sampledStateEstimator (rule B δ),?_⟩
  intro B δ hB hδ hd N μ _ D s hl P _ hreal
  obtain ⟨hw,hc⟩ := hrule B δ hB hδ hd μ
  constructor
  · rw [sampled_expectedWork μ D s hl (rule B δ) P hreal]
    exact hw (conditionalSign μ D s)
  · rw [sampled_failureProbability μ D s hl (rule B δ) P hreal]
    exact hc (conditionalSign μ D s)

end ThresholdHC.ContinuousObserved
