import ThresholdHC.Confidence.BatchSequence
import ThresholdHC.Confidence.InputLaw

noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Confidence
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open ThresholdHC.BlindUpper ThresholdHC.ObservableSimulation

/-- Exact pathwise identities when the finitely many local pilots finish. -/
theorem repeat_population_identities_pointwise (m L : ℕ)
    (r : RepeatSeed) (s : ℕ → ℕ → Bool) (a b : MedianIndex m → ℕ)
    (ha : ∀ i, firstSuccess (phaseMark L (r i.val) (fun j => s (Nat.pair i.val j)) 0) = a i)
    (hb : ∀ i, firstSuccess (phaseMark L (r i.val) (fun j => s (Nat.pair i.val j)) 1) = b i) :
    totalProcessWork (populationPath (repeatPolicy m L r) s) =
      ∑ i : MedianIndex m, cutoffBatchWork L (calibrationInputs (r,s) i.val) ∧
    repeatOutput m L (r,populationPath (repeatPolicy m L r) s) =
      median m (fun i => cutoffBatchOutput L (calibrationInputs (r,s) i.val)) := by
  let streams := fun i : MedianIndex m => fun j => s (Nat.pair i.val j)
  let words := fun i : MedianIndex m => fullBatchWord L (r i.val) (streams i) (a i) (b i)
  let final : RepeatState m := fun i =>
    (.stopped (phaseWords L (r i.val) (streams i) 2 (a i+b i+1)),[])
  have hstop : ∀ i, controlLabel (final i).1 = none := fun _ => rfl
  have hlocal : ∀ i, ∃ t, BatchConsumes L (r i.val) batchInitial
      (streams i) (words i) (final i) t := by
    intro i
    obtain ⟨t,ht⟩ := (fullBatch_plan L (r i.val) (streams i) (a i) (b i) (ha i) (hb i)).consumes
      (fullBatchLabels_nodup (a i) (b i)) (streams i) (fun _ _ => rfl)
    rw [callWords_fullBatchLabels] at ht
    exact ⟨t,ht⟩
  obtain ⟨xs,t,ht,hlen⟩ := repeat_all_consumes m L r s words final hstop hlocal
  have hfinal : repeatLabel final = none :=
    (repeatLabel_none_iff final).mpr ((selectActive_none_iff final).mpr hstop)
  have hpath : populationPath (repeatPolicy m L r) s = fun n => xs[n]? := ht.path_eq hfinal
  constructor
  · rw [hpath,totalProcessWork_word,hlen,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact fullBatch_work L (r i.val) (streams i) (a i) (b i) (ha i) (hb i)
  · rw [hpath]
    have hh : repeatPolicy m L r (processHistory (fun n => xs[n]?) xs.length) = none := by
      rw [processHistory_word]
      change repeatLabel (repeatRun m L r (repeatInitial m) xs) = none
      rw [ht.state_eq]
      exact hfinal
    rw [repeatOutput_at_halt m L r _ _ hh,processHistory_word,ht.state_eq]
    unfold repeatControlOutput
    congr 1
    funext i
    have ho := fullBatch_controller_output L (r i.val) (streams i) (a i) (b i) (ha i) (hb i)
    rw [run_full_batch L (r i.val) (streams i) (a i) (b i) (ha i) (hb i)] at ho
    exact ho

theorem repeat_pilots_terminate (m L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    ∀ᵐ z ∂originalSimulationLaw μ (repeatEstimator m L) q,
      ∀ i : MedianIndex m,
        firstSuccess (phaseMark L (repeatInputs z i.val).1 (repeatInputs z i.val).2 0) ≠ ⊤ ∧
        firstSuccess (phaseMark L (repeatInputs z i.val).1 (repeatInputs z i.val).2 1) ≠ ⊤ := by
  apply ae_all_iff.mpr
  intro i
  exact (repeatInput_preserving m L i.val μ q).quasiMeasurePreserving.ae (batch_pilots_terminate L μ q)

theorem repeat_population_identities (m L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    ∀ᵐ z ∂originalSimulationLaw μ (repeatEstimator m L) q,
      totalProcessWork (populationPath (repeatPolicy m L z.1) z.2) =
        ∑ i : MedianIndex m, cutoffBatchWork L (calibrationInputs z i.val) ∧
      repeatOutput m L (z.1,populationPath (repeatPolicy m L z.1) z.2) =
        median m (fun i => cutoffBatchOutput L (calibrationInputs z i.val)) := by
  filter_upwards [repeat_pilots_terminate m L μ q] with z hz
  exact repeat_population_identities_pointwise m L z.1 z.2 _ _
    (fun i => (ENat.natCast_toNat (hz i).1).symm)
    (fun i => (ENat.natCast_toNat (hz i).2).symm)

end ThresholdHC.Confidence
