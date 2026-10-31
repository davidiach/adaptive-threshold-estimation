import ThresholdHC.StoppingProgram.ObservableInformation
import ThresholdHC.StoppingProgram.AffinityRisk
import ThresholdHC.StoppingProgram.PriorContraction

/-! Risk lower bounds for arbitrary measurable functions of the actual seed
and observed finite prefix. Infinite risk is retained throughout. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem observable_prefix_risk {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (q r : SignLaw) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hw : expectedWork μ A (midpointPrior q r) ≤ ENNReal.ofReal B)
    (hab : signMean μ q.val ≤ signMean μ r.val)
    (f : R × (Fin N → Option Bool) → ℝ) (hf : Measurable f) :
    ENNReal.ofReal ((signMean μ r.val-signMean μ q.val)/2 *
      (1-(informationRatio μ N (midpointFourPriors q r)).toReal*B/4)) ≤
        max (rootMeanRisk (observablePrefixLaw μ A q N) f (signMean μ q.val))
          (rootMeanRisk (observablePrefixLaw μ A r N) f (signMean μ r.val)) := by
  have hi := observable_prefix_information_budget μ A q r N B hB hw
  have hr := affinity_rms_risk (observablePrefixLaw μ A q N) (observablePrefixLaw μ A r N)
    f hf (signMean μ q.val) (signMean μ r.val) hab
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hr
  have hgap : 0 ≤ (signMean μ r.val-signMean μ q.val)/2 := by positivity
  have hinfo : 1-(informationRatio μ N (midpointFourPriors q r)).toReal*B/4 ≤
      (hellingerAffinity (observablePrefixLaw μ A q N) (observablePrefixLaw μ A r N)).toReal := by
    linarith [hi]
  nlinarith [mul_le_mul_of_nonneg_left hinfo hgap]

end ThresholdHC.StoppingProgram
