import ThresholdHC.TypedConfidence.ParameterHybrid

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.TypedConfidence
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.CriticalEntropy
open ThresholdHC.ConfidenceTransfer

local instance : MeasurableSpace (Option Bool) := ⊤

/-- Expected genuine flips under the independent, label-dependent tape laws. -/
def parameterExpectedWork {m : ℕ} (κ : Fin m → Measure unitInterval)
    (pol : List Bool → Option (Fin m)) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ s, ((∑ t : Fin n, if ((populationSimulation pol n s).2 t).isSome then 1 else 0 : ℕ) : ℝ≥0∞)
    ∂Measure.pi (fun i => parameterTapeLaw (κ i))

def parameterLocalWork {m : ℕ} (κ : Fin m → Measure unitInterval)
    (pol : List Bool → Option (Fin m)) (n : ℕ) (i : Fin m) : ℝ≥0∞ :=
  ∫⁻ z, stoppedProcedureWork (localSimulationProcedure i n pol) z
    ∂(Measure.pi (fun j => parameterTapeLaw (κ j))).prod (parameterTapeLaw (κ i))

theorem parameter_local_work_le {m : ℕ} (κ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)]
    (pol : List Bool → Option (Fin m)) (n : ℕ) (i : Fin m) :
    parameterLocalWork κ pol n i ≤ n := by
  unfold parameterLocalWork
  calc
    _ ≤ ∫⁻ _, (n : ℝ≥0∞)
        ∂(Measure.pi (fun j => parameterTapeLaw (κ j))).prod (parameterTapeLaw (κ i)) := by
      apply lintegral_mono
      intro z
      change stoppedProcedureWork (localSimulationProcedure i n pol) z ≤ (n : ℝ≥0∞)
      rw [capped_transcript_work _ n z (localSimulationProcedure_capped i n pol z)]
      exact_mod_cast Nat.le_of_lt_succ (stoppedStatistic n
        (cappedTranscript (localSimulationProcedure i n pol) n z).2).1.isLt
    _ = _ := by simp

/-- Every genuine observation is charged exactly once, even under interleaved revisits. -/
theorem parameter_total_work {m : ℕ} (κ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)]
    (pol : List Bool → Option (Fin m)) (n : ℕ) :
    ∑ i : Fin m, parameterLocalWork κ pol n i = parameterExpectedWork κ pol n := by
  unfold parameterLocalWork parameterExpectedWork
  simp_rw [localSimulation_work,Function.update_eq_self]
  have hm (i : Fin m) : Measurable (fun s => ((populationSimulation pol n s).1 i : ℝ≥0∞)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).comp
      (measurable_populationSimulation_count n pol i)
  rw [← lintegral_finsetSum Finset.univ (fun i _ => hm i)]
  apply lintegral_congr
  intro s
  exact_mod_cast populationSimulation_total_work n pol s

theorem parameter_total_work_real {m : ℕ} (κ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)]
    (pol : List Bool → Option (Fin m)) (n : ℕ) :
    ∑ i : Fin m, (parameterLocalWork κ pol n i).toReal =
      (parameterExpectedWork κ pol n).toReal := by
  rw [← parameter_total_work]
  symm
  exact ENNReal.toReal_sum (fun i _ =>
    ne_top_of_le_ne_top (by simp) (parameter_local_work_le κ pol n i))

theorem parameter_expected_work_le {m : ℕ} (κ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)]
    (pol : List Bool → Option (Fin m)) (n : ℕ) :
    parameterExpectedWork κ pol n ≤ n := by
  unfold parameterExpectedWork
  calc
    _ ≤ ∫⁻ _, (n : ℝ≥0∞) ∂Measure.pi (fun i => parameterTapeLaw (κ i)) := by
      apply lintegral_mono
      intro s
      change ((∑ t : Fin n,
        if ((populationSimulation pol n s).2 t).isSome then 1 else 0 : ℕ) : ℝ≥0∞) ≤ (n : ℝ≥0∞)
      have h : (∑ t : Fin n,
          if ((populationSimulation pol n s).2 t).isSome then 1 else 0 : ℕ) ≤ ∑ _ : Fin n, 1 := by
        apply Finset.sum_le_sum
        intro t _
        split <;> omega
      exact_mod_cast (h.trans_eq (by simp))
    _ = _ := by simp

end ThresholdHC.TypedConfidence
