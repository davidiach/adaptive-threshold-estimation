import ThresholdHC.ResearchRouteA.SeparateBounds

/-! Non-vacuity at every positive gap, both signs, including the endpoint. -/

noncomputable section

namespace ThresholdHC.ResearchRouteA

open MeasureTheory ProbabilityTheory Filter ThresholdHC.Uniform713

theorem independent_constant_observations {A : Type*} [MeasurableSpace A]
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

theorem deterministic_gap_model (d : ℝ) (s : Bool) (hd : 0 < d) (hdhalf : d ≤ 1/2) :
    ObservationModel (Measure.dirac ()) (Kernel.const Unit (Measure.dirac ()))
      (fun (_ : ℕ) (_ : Unit) => coinMean d s) (fun (_ : Unit) => d)
      (fun (_ : Unit) => s) := by
  constructor
  · intro i
    exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · filter_upwards with θ
    exact ⟨hd, hdhalf⟩
  · filter_upwards with θ
    intro i
    filter_upwards with ω
    cases s <;> simp only [coinMean, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc] <;>
      constructor <;> linarith
  · filter_upwards with θ
    intro i
    simp
  · filter_upwards with θ
    exact independent_constant_observations _ (fun _ => coinMean d s)
  · exact integrable_const _

theorem deterministic_gap_separate_bounds (d : ℝ) (s : Bool)
    (hd : 0 < d) (hdhalf : d ≤ 1/2) :
    let ν : Measure Unit := Measure.dirac ()
    let κ : Kernel Unit Unit := Kernel.const Unit (Measure.dirac ())
    let X := fun (_ : ℕ) (_ : Unit) => coinMean d s
    MemLp (@uniformEstimator Unit Unit X) 2 (mixtureLaw ν κ) ∧
    Integrable (@uniformWork Unit Unit X) (mixtureLaw ν κ) ∧
    (∫ x, (uniformEstimator X x) ^ 2 ∂mixtureLaw ν κ) ≤ 23 / d ∧
    (∫ x, uniformWork X x ∂mixtureLaw ν κ) ≤ 31 / d := by
  simpa only [integral_const, measureReal_def, Measure.dirac_apply_of_mem,
    Set.mem_univ, ENNReal.toReal_one, one_smul, div_eq_mul_inv] using
    separate_moment_bounds Unit Unit (Measure.dirac ())
      (Kernel.const Unit (Measure.dirac ())) (fun (_ : ℕ) (_ : Unit) => coinMean d s)
      (fun (_ : Unit) => d) (fun (_ : Unit) => s) (deterministic_gap_model d s hd hdhalf)

end ThresholdHC.ResearchRouteA

#print axioms ThresholdHC.ResearchRouteA.independent_constant_observations
#print axioms ThresholdHC.ResearchRouteA.deterministic_gap_model
#print axioms ThresholdHC.ResearchRouteA.deterministic_gap_separate_bounds
