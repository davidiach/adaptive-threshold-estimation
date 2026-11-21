import ThresholdHC.NonintervalSelection.Table

/-! The noninterval optimal assignment of the rare-event paper
(`paper/v6/rare-discussion.tex`, paragraph A noninterval optimal assignment):
the five target statements of `Specification.lean`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.NonintervalSelection
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail ThresholdHC.FiniteLawCertificates

/-- The law is a probability law, `h = 1/1024`, every atom lies above `h`, and
every hard retained part is a submeasure. -/
theorem setup : SetupStatement := by
  refine ⟨?_, by rw [sqrt_budget], ?_, retained_le⟩
  · rw [law_eq]
    exact atomicMeasure_probability _ _ weights_nonneg weights_sum
  · intro i
    fin_cases i <;> norm_num [atoms]

/-- The paper's table: all eight rows, each with a strict open enclosure of the
inner cost divided by `h`. -/
theorem enclosure : EnclosureStatement := by
  refine ⟨enclosures_complete, ?_⟩
  intro e he
  obtain ⟨h1, h2⟩ := enclosures_bounds e he
  rw [objective_toReal _ (J_lt_cap _), sqrt_budget]
  constructor
  · rw [lt_div_iff₀ (by norm_num)]
    linarith
  · rw [div_lt_iff₀ (by norm_num)]
    linarith

/-- The hard retained set `{1/2, 1/8}` is the unique minimum of the eight. -/
theorem unique_hard_minimum : UniqueHardMinimumStatement :=
  objective_optimal_lt

/-- The cap is inactive and the original functional has the same optimizer,
the restriction of the law to `{1/2, 1/8}`. -/
theorem original_optimizer : OriginalOptimizerStatement := by
  refine ⟨?_, selection_eq_optimal, ?_⟩
  · rw [objective_eq optimalMask (J_lt_cap _)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (J_lt_cap _)
  · obtain ⟨m, hm, hmi⟩ := restrict_eq {d : Gap | (d : ℝ) = 1/2 ∨ (d : ℝ) = 1/8}
    rw [hm]
    congr 1
    funext i
    rw [Bool.eq_iff_iff, hmi i]
    fin_cases i <;> norm_num [atoms, optimalMask]

/-- No interval retention is optimal: the intervening atom has positive mass, the
optimal mask is not cut out by an interval, and every interval retention costs
strictly more than the original functional. -/
theorem noninterval : NonintervalStatement := by
  refine ⟨by norm_num [masses], optimalMask_not_interval, ?_⟩
  intro I hI
  obtain ⟨m, hm, hmi⟩ := restrict_eq {d : Gap | (d : ℝ) ∈ I}
  rw [hm, selection_eq_optimal]
  apply objective_optimal_lt
  intro hmo
  apply optimalMask_not_interval
  refine ⟨I, hI, fun i => ?_⟩
  rw [← hmo, hmi i]
  exact Iff.rfl

end ThresholdHC.NonintervalSelection
