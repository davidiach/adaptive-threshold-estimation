import ThresholdHC.CriticalUpper.FixedExecution
import ThresholdHC.BlindUpper.ActualBatch

/-! Actual terminal output and total flip count equal the independent call quantities. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory ProbabilityTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open scoped ENNReal

theorem fixedOutput_at_halt (ρ : ℝ) (N : ℕ) (r : CriticalSeed) (x : ProcessTape) (n : ℕ)
    (hn : fixedPolicy ρ N r (processHistory x n) = none) :
    fixedOutput ρ N (r,x) = fixedWordsOutput ρ r (fixedRun ρ N r ([],[]) (processHistory x n)).1 := by
  have hmark : (fixedPolicy ρ N r (processHistory x n)).isNone = true := by rw [hn]; rfl
  obtain ⟨k,hkn,hk⟩ := firstSuccess_finite_le
    (fun j => (fixedPolicy ρ N r (processHistory x j)).isNone) n hmark
  have hkstop : fixedPolicy ρ N r (processHistory x k) = none :=
    Option.isNone_iff_eq_none.mp ((firstSuccess_eq _ _).mp hk).1
  have hlen : N ≤ (fixedRun ρ N r ([],[]) (processHistory x k)).1.length := by
    by_contra h
    have hl : (fixedRun ρ N r ([],[]) (processHistory x k)).1.length < N := Nat.lt_of_not_ge h
    unfold fixedPolicy fixedLabel at hkstop
    rw [ite_eq_left hl] at hkstop
    cases hkstop
  have he : fixedRun ρ N r ([],[]) (processHistory x n) =
      fixedRun ρ N r ([],[]) (processHistory x k) := by
    conv_lhs => rw [show n = k+(n-k) by omega,processHistory_add,fixedRun_append]
    exact fixedRun_absorbs ρ N r _ hlen _
  change fixedWordsOutput ρ r (fixedRun ρ N r ([],[])
    (processHistory x (fixedHaltTime ρ N (r,x)).toNat)).1 = _
  rw [show fixedHaltTime ρ N (r,x) = k from hk]
  simp only [ENat.toNat_natCast]
  rw [he]

theorem fixedCallWords_get (ρ : ℝ) (r : CriticalSeed) (s : ℕ → ℕ → Bool) (n : ℕ) (i : Fin n) :
    (fixedCallWords ρ r s n)[i.val]'(by simp) = fixedCallWord ρ r s i.val := by
  simp [fixedCallWords]

theorem fixedWordsOutput_calls (ρ : ℝ) (r : CriticalSeed) (s : ℕ → ℕ → Bool) (n : ℕ) :
    fixedWordsOutput ρ r (fixedCallWords ρ r s (n+1)) =
      criticalAverage ρ n (criticalCalls (r,s)) := by
  unfold fixedWordsOutput
  have hval (i : ℕ) (hi : i < (fixedCallWords ρ r s (n+1)).length) :
      coupledValue ρ (r i) (completeList (fixedCallWords ρ r s (n+1))[i]) =
        coupledValue ρ (r i) (s i) := by
    rw [fixedCallWords_get ρ r s (n+1) ⟨i,by simpa using hi⟩]
    exact coupledValue_observed ρ (r i) (s i)
  simp_rw [hval]
  have hsum : (∑ i : Fin (fixedCallWords ρ r s (n+1)).length, coupledValue ρ (r i.val) (s i.val)) =
      ∑ i : Fin (n+1), coupledValue ρ (r i.val) (s i.val) :=
    Fintype.sum_equiv (finCongr (fixedCallWords_length ρ r s (n+1))) _ _ (by intro i; rfl)
  rw [hsum,fixedCallWords_length]
  unfold criticalAverage productionAverage finiteAverage productionPrefix criticalCalls
  rw [criticalUnbiasedProcedure_output]
  simp only [estimator,coupledValue,Nat.cast_add,Nat.cast_one]
  ring

theorem fixed_population_output (ρ : ℝ) (r : CriticalSeed) (s : ℕ → ℕ → Bool) (n : ℕ) :
    fixedOutput ρ (n+1) (r,populationPath (fixedPolicy ρ (n+1) r) s) =
      criticalAverage ρ n (criticalCalls (r,s)) := by
  rw [fixed_populationPath_eq]
  have hh : fixedPolicy ρ (n+1) r
      (processHistory (fun j => (fixedTranscript ρ r s (n+1))[j]?) (fixedTranscript ρ r s (n+1)).length) = none := by
    rw [processHistory_word]
    change fixedLabel (n+1) (fixedRun ρ (n+1) r ([],[]) (fixedTranscript ρ r s (n+1))) = none
    rw [(fixedConsumes_prefix ρ (n+1) r s (n+1) le_rfl).state_eq]
    simp [fixedLabel]
  rw [fixedOutput_at_halt ρ (n+1) r _ _ hh,processHistory_word,
    (fixedConsumes_prefix ρ (n+1) r s (n+1) le_rfl).state_eq]
  exact fixedWordsOutput_calls ρ r s n

theorem fixedTranscript_length (ρ : ℝ) (r : CriticalSeed) (s : ℕ → ℕ → Bool) (N : ℕ) :
    (fixedTranscript ρ r s N).length = ∑ i ∈ Finset.range N, coupledCost ρ (r i) (s i) := by
  induction N with
  | zero => simp [fixedTranscript,fixedCallWords]
  | succ N ih =>
    rw [fixedTranscript_succ,List.length_append,ih,Finset.sum_range_succ]
    simp [fixedCallWord]

theorem fixed_population_work (ρ : ℝ) (r : CriticalSeed) (s : ℕ → ℕ → Bool) (n : ℕ) :
    totalProcessWork (populationPath (fixedPolicy ρ (n+1) r) s) =
      criticalArrayWork ρ n (criticalCalls (r,s)) := by
  rw [fixed_populationPath_eq,totalProcessWork_word,fixedTranscript_length,Nat.cast_sum]
  unfold criticalArrayWork criticalCalls
  simp_rw [criticalUnbiasedProcedure_work,ENNReal.ofReal_natCast]
  exact (Fin.sum_univ_eq_sum_range (fun i => (coupledCost ρ (r i) (s i) : ℝ≥0∞)) (n+1)).symm

end ThresholdHC.CriticalUpper
