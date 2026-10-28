import ThresholdHC.BlindUpper.ActualBatch

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.ObservableSimulation
open scoped ENNReal
open ThresholdHC.Tier6

theorem measurable_paddedMark (L : ℕ) : Measurable (paddedMark L) :=
  measurable_costParameter _ _ _ _ (measurable_paddedRealCost L)

theorem paddedMark_mean_pos (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    0 < (meanParameter (callMeasure μ q) (paddedMark L) (measurable_paddedMark L) : ℝ) := by
  unfold paddedMark
  rw [mean_costParameter _ _ _ _ _ (measurable_paddedRealCost L)]
  exact div_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (paddedCutoff_work_lower L μ q))
    (by positivity)

theorem batch_pilots_terminate (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    ∀ᵐ z ∂originalSimulationLaw μ (batchEstimator L) q,
      firstSuccess (phaseMark L z.1 z.2 0) ≠ ⊤ ∧ firstSuccess (phaseMark L z.1 z.2 1) ≠ ⊤ := by
  let ν := callMeasure μ q
  let π := markedSequenceLaw ν
  have hp : meanParameter ν (paddedMark L) (measurable_paddedMark L) ≠ 0 := by
    intro h
    have ht := paddedMark_mean_pos L μ q
    change 0 < (meanParameter ν (paddedMark L) (measurable_paddedMark L) : ℝ) at ht
    simp [h] at ht
  have ht := pilot_terminates ν (paddedMark L) (measurable_paddedMark L) hp
  have h₀ : ∀ᵐ z ∂π.prod π, firstSuccess (markedTape (paddedMark L) z.1) ≠ ⊤ :=
    Measure.quasiMeasurePreserving_fst.ae ht
  have h₁ : ∀ᵐ z ∂π.prod π, firstSuccess (markedTape (paddedMark L) z.2) ≠ ⊤ :=
    Measure.quasiMeasurePreserving_snd.ae ht
  have hcal : ∀ᵐ z ∂calibrationLaw ν,
      firstSuccess (markedTape (paddedMark L) z.1.1) ≠ ⊤ ∧
      firstSuccess (markedTape (paddedMark L) z.1.2) ≠ ⊤ :=
    Measure.quasiMeasurePreserving_fst.ae (h₀.and h₁)
  exact (batchInput_preserving μ q).quasiMeasurePreserving.ae hcal

/-- Actual work and output identities under the population law, with pilot
termination derived from its independent seed law. -/
theorem batch_population_identities (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    ∀ᵐ z ∂originalSimulationLaw μ (batchEstimator L) q,
      totalProcessWork (populationPath (batchPolicy L z.1) z.2) = cutoffBatchWork L (batchInput z) ∧
      batchOutput L (z.1,populationPath (batchPolicy L z.1) z.2) = cutoffBatchOutput L (batchInput z) := by
  filter_upwards [batch_pilots_terminate L μ q] with z hz
  have h₀ := (ENat.natCast_toNat hz.1).symm
  have h₁ := (ENat.natCast_toNat hz.2).symm
  exact ⟨batch_population_work L z.1 z.2 _ _ h₀ h₁,batch_population_output L z.1 z.2 _ _ h₀ h₁⟩

theorem measurable_cutoffBatchWork (L : ℕ) : Measurable (cutoffBatchWork L) :=
  measurable_calibrationWork _ (measurable_paddedMark L) _ (measurable_paddedRealCost L)

theorem measurable_cutoffBatchOutput (L : ℕ) : Measurable (cutoffBatchOutput L) :=
  measurable_calibrationOutput _ (measurable_paddedMark L) _ (measurable_cutoffValue L)

/-- Equality of the original experiment's actual expected flips and the
calibrated independent-call cost. -/
theorem batch_expectedWork_eq (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    expectedWork μ (batchEstimator L) q =
      ∫⁻ z, cutoffBatchWork L z ∂calibrationLaw (callMeasure μ q) := by
  rw [original_expectedWork_simulation]
  calc
    _ = ∫⁻ z, cutoffBatchWork L (batchInput z) ∂originalSimulationLaw μ (batchEstimator L) q := by
      apply lintegral_congr_ae
      filter_upwards [batch_population_identities L μ q] with z hz
      exact hz.1
    _ = _ := (batchInput_preserving μ q).lintegral_comp (measurable_cutoffBatchWork L)

/-- Equality of extended squared risks; no finite-risk assumption is used. -/
theorem batch_squaredRisk_eq (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (a : ℝ) :
    squaredRisk (experimentLaw μ (batchEstimator L) q) (populationOutput (batchEstimator L)) a =
      ∫⁻ z, ENNReal.ofReal ((cutoffBatchOutput L z-a)^2) ∂calibrationLaw (callMeasure μ q) := by
  rw [original_squaredRisk_simulation]
  calc
    _ = ∫⁻ z, ENNReal.ofReal ((cutoffBatchOutput L (batchInput z)-a)^2)
        ∂originalSimulationLaw μ (batchEstimator L) q := by
      apply lintegral_congr_ae
      filter_upwards [batch_population_identities L μ q] with z hz
      change ENNReal.ofReal ((batchOutput L (z.1,populationPath (batchPolicy L z.1) z.2)-a)^2) = _
      rw [hz.2]
    _ = _ := (batchInput_preserving μ q).lintegral_comp
      (((measurable_cutoffBatchOutput L).sub measurable_const).pow_const 2).ennreal_ofReal

theorem batch_uniformBudget (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    UniformBudget μ (batchEstimator L) (4*(2 : ℝ)^L) := by
  intro q
  rw [batch_expectedWork_eq]
  exact cutoffBatch_budget L μ q

theorem batch_squaredRisk_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    squaredRisk (experimentLaw μ (batchEstimator L) q) (populationOutput (batchEstimator L))
        (signMean μ q.val) ≤ ENNReal.ofReal (12751*(modulus μ (1/Real.sqrt ((2 : ℝ)^L)))^2) := by
  rw [batch_squaredRisk_eq]
  exact cutoffBatch_mse L μ q

end ThresholdHC.BlindUpper
