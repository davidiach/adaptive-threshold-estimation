import ThresholdHC.RobustContinuationForms.NamedPlanner
import ThresholdHC.RobustContinuationForms.InducedSign
import ThresholdHC.RobustContinuationForms.CorrectTimes

/-! The literal forms of the robust continuation: one theorem per target
statement of `ThresholdHC.RobustContinuationForms.Specification`. -/

namespace ThresholdHC.RobustContinuationForms

/-- (i-a) The named robust planner under every coupled true law. -/
theorem robust_tight_planner_output : RobustTightPlannerOutputStatement :=
  robust_tight_planner_output_proof

/-- (i-b) The named robust planner under every CDF-dominated true law. -/
theorem cdf_robust_tight_planner_output : CDFRobustTightPlannerOutputStatement :=
  cdf_robust_tight_planner_output_proof

/-- (i-c) The named planner on the named reference design. -/
theorem robust_exact_planner_output : RobustExactPlannerOutputStatement :=
  robust_exact_planner_output_proof

/-- (i-a, large atom) The constant `ρ/2` when the reference mass at zero is at
least `ρ`. -/
theorem robust_large_atom_output : RobustLargeAtomOutputStatement :=
  robust_large_atom_output_proof

/-- (ii) The induced reference sign allocation. -/
theorem induced_sign_allocation : InducedSignAllocationStatement :=
  induced_sign_allocation_proof

/-- (iii-a) The race work is at most twice the earlier correct-sign time. -/
theorem correct_time_race_bound : CorrectTimeRaceBoundStatement :=
  correct_time_race_bound_proof

/-- (iii-b) Both correct-sign times decrease in the sign-directed order. -/
theorem correct_time_antitone : CorrectTimeAntitoneStatement :=
  correct_time_antitone_proof

/-- (iii-c) `(UA15)` under the common-uniform coupling. -/
theorem coupled_correct_time_work : CoupledCorrectTimeWorkStatement :=
  coupled_correct_time_work_proof

/-- (iii-c, gaps) `(UA15)` for a reference gap below the true gap. -/
theorem coupled_gap_correct_time_work : CoupledGapCorrectTimeWorkStatement :=
  coupled_gap_correct_time_work_proof

/-- (iii-c, zero atom) `(UA15)` for the reference zero atom. -/
theorem coupled_zero_atom_correct_time_work : CoupledZeroAtomCorrectTimeWorkStatement :=
  coupled_zero_atom_correct_time_work_proof

/-- (iii-d) `(UA15)` for the level race of the reference design. -/
theorem reference_race_correct_time_work : ReferenceRaceCorrectTimeWorkStatement :=
  reference_race_correct_time_work_proof

end ThresholdHC.RobustContinuationForms
