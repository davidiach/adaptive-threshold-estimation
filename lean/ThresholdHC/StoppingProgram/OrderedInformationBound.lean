import ThresholdHC.StoppingProgram.OrderedHellinger
import ThresholdHC.StoppingProgram.OrderedWork
import ThresholdHC.StoppingProgram.InformationBound

/-! Uniform local information bound for arbitrary seeded ordered stopping
procedures, using their actual midpoint expected physical work. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation
open ThresholdHC.Tier6 (Gap SignLaw)

theorem ordered_stopped_hellinger_work {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (q r : SignLaw) (A : StoppedProcedure R E) (N : ℕ) (hcap : ∀ z, A.stop z ≤ N) :
    stoppedHellinger μ ν q r A N ≤ ((informationRatio μ N (midpointFourPriors q r)).toReal/4)*
      (populationExpectedWork μ ν (gapParameter false) (gapParameter true)
        (signUnit (midpointPrior q r)) A).toReal := by
  have hf := orderedFlow_cone ν A N hcap
  have hW := countMean_nonneg μ (midpointPrior q r) (orderedFlow ν A N).continueWeight hf.continue_nonneg
  have hI := flowInformation_toReal_le μ (midpointFourPriors q r) (orderedFlow ν A N) hf
    (midpoint_informationRatio_finite μ N q r) hW le_rfl
  have hh := (orderedFlow_midpoint_hellinger μ ν q r A N hcap).1
  rw [orderedFlow_actual_work μ ν (midpointPrior q r) A N hcap,ENNReal.toReal_ofReal hW]
  nlinarith [hI]

end ThresholdHC.StoppingProgram
