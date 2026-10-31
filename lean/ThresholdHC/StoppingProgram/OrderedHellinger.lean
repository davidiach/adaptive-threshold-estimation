import ThresholdHC.StoppingProgram.OrderedAffinity
import ThresholdHC.StoppingProgram.OrderedRewards
import ThresholdHC.StoppingProgram.MidpointInformation

/-! Actual stopped-transcript Hellinger distance and midpoint flow
information agree within the sharp factors four and eight. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation
open ThresholdHC.Tier6 (Gap SignLaw)

def stoppedHellinger {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure Gap) (ν : Measure R) (q r : SignLaw) (A : StoppedProcedure R E) (N : ℕ) : ℝ :=
  1-(hellingerAffinity
    (cappedTranscriptLaw μ ν (gapParameter false) (gapParameter true) (signUnit q) A N)
    (cappedTranscriptLaw μ ν (gapParameter false) (gapParameter true) (signUnit r) A N)).toReal

theorem stoppedReferenceSum_total {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (q : SignLaw) (A : StoppedProcedure R E) (N : ℕ) (hcap : ∀ z, A.stop z ≤ N) :
    stoppedReferenceSum ν A N (prefixCoefficient μ q) = 1 := by
  let P := cappedTranscriptLaw μ ν (gapParameter false) (gapParameter true) (signUnit q) A N
  letI : IsProbabilityMeasure P := cappedTranscriptLaw_probability μ ν _ _ _
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q) A N
  have he := original_stopped_word_integral μ ν q A N hcap (fun _ => 1)
  change (∫ _z, (1:ℝ) ∂P) = _ at he
  simpa [stoppedReferenceSum] using he.symm

theorem stoppedHellinger_squares {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (q r : SignLaw) (A : StoppedProcedure R E) (N : ℕ) (hcap : ∀ z, A.stop z ≤ N) :
    2*stoppedHellinger μ ν q r A N = stoppedReferenceSum ν A N
      (fun n k => (Real.sqrt (prefixCoefficient μ q n k)-Real.sqrt (prefixCoefficient μ r n k))^2) := by
  have hq := stoppedReferenceSum_total μ ν q A N hcap
  have hr := stoppedReferenceSum_total μ ν r A N hcap
  rw [stoppedHellinger,original_stopped_word_affinity μ ν q r A N hcap]
  have he : stoppedReferenceSum ν A N
      (fun n k => (Real.sqrt (prefixCoefficient μ q n k)-Real.sqrt (prefixCoefficient μ r n k))^2) =
      stoppedReferenceSum ν A N (prefixCoefficient μ q)+stoppedReferenceSum ν A N (prefixCoefficient μ r)-
        2*(∑ w : CappedWord N, ν.real (stoppedSeedCell A w.2 Set.univ)*
          Real.sqrt (prefixCoefficient μ q w.1.val (wordHeads w.2)*prefixCoefficient μ r w.1.val (wordHeads w.2))) := by
    unfold stoppedReferenceSum
    rw [← Finset.sum_add_distrib,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro w _
    rw [Real.sqrt_mul (prefixCoefficient_nonneg μ q _ _)]
    dsimp only
    rw [sub_sq,Real.sq_sqrt (prefixCoefficient_nonneg μ q w.1.val (wordHeads w.2)),
      Real.sq_sqrt (prefixCoefficient_nonneg μ r w.1.val (wordHeads w.2))]
    ring
  rw [he,hq,hr]
  ring

theorem orderedFlow_midpoint_hellinger {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (q r : SignLaw) (A : StoppedProcedure R E) (N : ℕ) (hcap : ∀ z, A.stop z ≤ N) :
    4*stoppedHellinger μ ν q r A N ≤ (flowInformation μ (midpointFourPriors q r) (orderedFlow ν A N)).toReal ∧
    (flowInformation μ (midpointFourPriors q r) (orderedFlow ν A N)).toReal ≤ 8*stoppedHellinger μ ν q r A N := by
  rw [orderedFlow_information μ ν _ A N hcap (fun n k _ hk => midpoint_prefixInformation_finite μ q r n k hk)]
  have he := stoppedHellinger_squares μ ν q r A N hcap
  have hlo : 2*stoppedReferenceSum ν A N
      (fun n k => (Real.sqrt (prefixCoefficient μ q n k)-Real.sqrt (prefixCoefficient μ r n k))^2) ≤
      stoppedReferenceSum ν A N (prefixReward μ (midpointFourPriors q r)) := by
    unfold stoppedReferenceSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w _
    rw [midpoint_prefixReward μ q r _ _ (wordHeads_le_length w.2)]
    have hh := mul_le_mul_of_nonneg_left (midpoint_quadratic_hellinger _ _
      (prefixCoefficient_nonneg μ q w.1.val (wordHeads w.2)) (prefixCoefficient_nonneg μ r w.1.val (wordHeads w.2))).1
        (show 0 ≤ ν.real (stoppedSeedCell A w.2 Set.univ) from measureReal_nonneg)
    nlinarith [hh]
  have hhi : stoppedReferenceSum ν A N (prefixReward μ (midpointFourPriors q r)) ≤
      4*stoppedReferenceSum ν A N
        (fun n k => (Real.sqrt (prefixCoefficient μ q n k)-Real.sqrt (prefixCoefficient μ r n k))^2) := by
    unfold stoppedReferenceSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w _
    rw [midpoint_prefixReward μ q r _ _ (wordHeads_le_length w.2)]
    have hh := mul_le_mul_of_nonneg_left (midpoint_quadratic_hellinger _ _
      (prefixCoefficient_nonneg μ q w.1.val (wordHeads w.2)) (prefixCoefficient_nonneg μ r w.1.val (wordHeads w.2))).2
        (show 0 ≤ ν.real (stoppedSeedCell A w.2 Set.univ) from measureReal_nonneg)
    nlinarith [hh]
  constructor <;> linarith

end ThresholdHC.StoppingProgram
