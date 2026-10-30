import ThresholdHC.StoppingProgram.OrderedStoppedLaw
import ThresholdHC.StoppingProgram.TableStatistics
import ThresholdHC.StoppingProgram.PrefixInformation
import ThresholdHC.StoppingProgram.FlowCostMoment

/-! Seed-and-stopped-word reward sums agree exactly with the aggregated
flow's stopping rewards, including information and stopping depth. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy
open ThresholdHC.Tier6 (Gap SignLaw)

def stoppedReferenceSum {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) (A : StoppedProcedure R E) (N : ℕ) (F : ℕ → ℕ → ℝ) : ℝ :=
  ∑ w : CappedWord N, ν.real (stoppedSeedCell A w.2 Set.univ)*F w.1.val (wordHeads w.2)

theorem orderedFlow_stopped_rewards {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E) (N : ℕ)
    (hcap : ∀ z, A.stop z ≤ N) (F : ℕ → ℕ → ℝ) (hroot : F 0 0 = 0) :
    stoppedReferenceSum ν A N F = ∑ n ∈ Finset.range (N+1), rawLayer (orderedFlow ν A N).stopWeight F n := by
  have hrow (n : ℕ) (hn : n ≤ N) :
      (∑ w : Fin n → Bool, ν.real (stoppedSeedCell A w Set.univ)*F n (wordHeads w)) =
        rawLayer (orderedFlow ν A N).stopWeight F n := by
    have hweights : (∑ w : Fin n → Bool, ν.real (stoppedSeedCell A w Set.univ)*F n (wordHeads w)) =
        ∑ w : Fin n → Bool, orderedStopMass ν A w*F n (wordHeads w) := by
      apply Finset.sum_congr rfl
      intro w _
      by_cases hn0 : n = 0
      · subst n
        have hh : wordHeads w = 0 := by have h := wordHeads_le_length w; omega
        simp only [hh,hroot,mul_zero]
      · rw [orderedStopMass_eq ν A hcap (by omega)]
    rw [hweights,sum_words_by_heads]
    unfold rawLayer orderedFlow
    apply Finset.sum_congr rfl
    intro k _
    have hout : ∀ n k, n < k → orderedCountStop ν A n k = 0 :=
      fun n k hk => headCountMass_outside _ k hk
    rw [raw_normalizedRawFlow_stop (orderedCountStop ν A) (orderedCountContinue ν A) hout n k hn]
    rfl
  unfold stoppedReferenceSum
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ n : Fin (N+1), rawLayer (orderedFlow ν A N).stopWeight F n.val := by
      apply Finset.sum_congr rfl
      intro n _
      exact hrow n.val (by have h := n.isLt; omega)
    _ = _ := Fin.sum_univ_eq_sum_range (fun n => rawLayer (orderedFlow ν A N).stopWeight F n) _

theorem orderedFlow_information {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (Q : FourPriors) (A : StoppedProcedure R E) (N : ℕ) (hcap : ∀ z, A.stop z ≤ N)
    (hfin : ∀ n k, n ≤ N → k ≤ n → prefixInformation μ Q n k ≠ ⊤) :
    (flowInformation μ Q (orderedFlow ν A N)).toReal = stoppedReferenceSum ν A N (prefixReward μ Q) := by
  rw [flowInformation_toReal_raw μ Q _ (orderedFlow_cone ν A N hcap) hfin,
    orderedFlow_stopped_rewards ν A N hcap _]
  rw [prefixReward,prefixInformation_root,ENNReal.toReal_zero]

theorem orderedFlow_work_moment {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (q : SignLaw) (A : StoppedProcedure R E) (N : ℕ) (hcap : ∀ z, A.stop z ≤ N) :
    stoppedReferenceSum ν A N (fun n k => n*prefixCoefficient μ q n k) =
      countMean μ q (orderedFlow ν A N).continueWeight := by
  rw [orderedFlow_stopped_rewards ν A N hcap _ (by simp)]
  simp only [rawLayer_mul_depth]
  have he := rawLayer_countMean μ q (fun s => (s.1.val:ℝ)*(orderedFlow ν A N).stopWeight s)
  simp only [rawLayer_depth_weight] at he
  rw [he,flow_work_stopping_depth μ q _ (orderedFlow_cone ν A N hcap)]

end ThresholdHC.StoppingProgram
