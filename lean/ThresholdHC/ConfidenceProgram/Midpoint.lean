import ThresholdHC.ConfidenceTransfer.Testing
import ThresholdHC.StoppingProgram.OrderedInformationBound
import ThresholdHC.StoppingProgram.PriorContraction

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ConfidenceProgram
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation
open ThresholdHC.ConfidenceTransfer ThresholdHC.StoppingProgram

private theorem reverse_hellinger {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure Gap) (ν : Measure R) (q r : SignLaw) (A : StoppedProcedure R E) (N : ℕ) :
    stoppedHellinger μ ν r q A N = stoppedHellinger μ ν q r A N := by
  unfold stoppedHellinger hellingerAffinity
  rw [add_comm (cappedTranscriptLaw _ _ _ _ (signUnit r) _ _)]
  congr 2
  apply lintegral_congr; intro x; rw [mul_comm]

private theorem midpoint_le_twice_quarter {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (f : Flow N) (hf : FlowCone f) :
    countMean μ (StoppingProgram.midpointPrior q r) f.continueWeight ≤
      2*countMean μ (smoothedSign r q) f.continueWeight := by
  have he : smoothedSign r q = mixPrior r q (3/4) (by norm_num) := by
    apply Subtype.ext; funext d
    change (3*r.val d+q.val d)/4 = 3/4*r.val d+(1-3/4)*q.val d
    ring
  unfold countMean
  rw [he,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  rw [midpointPrior_countCoefficient,mixPrior_countCoefficient]
  nlinarith only [mul_nonneg (countCoefficient_nonneg μ r s) (hf.continue_nonneg s)]

/-- A bound J on every ordinary midpoint ratio supplies the Hellinger premise
at J/2 charged to the high-quarter reference, for every randomized stopped rule. -/
theorem midpoint_reference_bound (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) {J : ℝ} (hJ : 0 ≤ J)
    (hI : ∀ n, informationRatio μ n (midpointFourPriors q r) ≤ ENNReal.ofReal J) :
    LocalReferenceWorkBound μ (gapParameter false) (gapParameter true) (signUnit r) (signUnit q) (J/2) := by
  intro R E _ _ ν _ A n hn
  change stoppedHellinger μ ν r q A n ≤ (J/2)*(populationExpectedWork μ ν
    (gapParameter false) (gapParameter true) (signUnit (smoothedSign r q)) A).toReal
  rw [reverse_hellinger]
  have h := ordered_stopped_hellinger_work μ ν q r A n hn
  have hf := orderedFlow_cone ν A n hn
  have hi := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hI n)
  rw [ENNReal.toReal_ofReal hJ] at hi
  have work (u : SignLaw) : (populationExpectedWork μ ν (gapParameter false) (gapParameter true) (signUnit u) A).toReal =
      countMean μ u (orderedFlow ν A n).continueWeight := by
    rw [orderedFlow_actual_work μ ν u A n hn,ENNReal.toReal_ofReal (countMean_nonneg _ _ _ hf.continue_nonneg)]
  rw [work] at h
  rw [work]
  have hmid := midpoint_le_twice_quarter μ q r _ hf
  have hm := countMean_nonneg μ (StoppingProgram.midpointPrior q r) _ hf.continue_nonneg
  nlinarith only [h,mul_le_mul_of_nonneg_right hi hm,mul_le_mul_of_nonneg_left hmid hJ]

end ThresholdHC.ConfidenceProgram
