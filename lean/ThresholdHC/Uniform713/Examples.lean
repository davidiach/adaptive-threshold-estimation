import ThresholdHC.Uniform713.Specification

/-! A concrete observation model proves that the natural hypotheses are satisfiable. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter

namespace ThresholdHC.Uniform713

private theorem independent_constant_family {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (c : ℕ → ℝ) :
    iIndepFun (fun i (_ : A) => c i) μ := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have ih' := ih (fun i hi => hsets i (Finset.mem_insert_of_mem hi))
    by_cases h : c a ∈ sets a
    · simpa [ha, Set.preimage_const_of_mem h] using ih'
    · simp [ha, Set.preimage_const_of_notMem h]

/-- The positive endpoint is the Bernoulli(1) model on a one-point tape space. -/
theorem deterministic_positive_model :
    ObservationModel (Measure.dirac ()) (Kernel.const Unit (Measure.dirac ()))
      (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) (fun (_ : Unit) => (1 / 2 : ℝ))
      (fun (_ : Unit) => true) := by
  constructor
  · intro i
    exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · filter_upwards with θ
    norm_num
  · filter_upwards with θ
    intro i
    filter_upwards with ω
    norm_num
  · filter_upwards with θ
    intro i
    norm_num [coinMean]
  · filter_upwards with θ
    exact independent_constant_family _ (fun _ => 1)
  · exact integrable_const _

end ThresholdHC.Uniform713

#print axioms ThresholdHC.Uniform713.deterministic_positive_model
