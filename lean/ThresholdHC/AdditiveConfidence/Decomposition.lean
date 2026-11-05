import ThresholdHC.AdditiveConfidence.HalfDensity

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace ThresholdHC.AdditiveConfidence
open ThresholdHC.Tier6

/-- A finite submeasure decomposition retains the common all-negative residual.
The component laws may have overlapping support. -/
structure GapMixture (I : Type) [Fintype I] (μ : Measure Gap) where
  weight : I → ℝ≥0
  law : I → Measure Gap
  law_probability : ∀ i, IsProbabilityMeasure (law i)
  residual : Measure Gap
  eq_measure : μ = residual+∑ i, weight i • law i

attribute [instance] GapMixture.law_probability

theorem GapMixture.residual_le {I : Type} [Fintype I] {μ : Measure Gap}
    (M : GapMixture I μ) : M.residual ≤ μ := by
  exact (show M.residual ≤ M.residual+∑ i, M.weight i • M.law i from
    Measure.le_add_right le_rfl).trans_eq M.eq_measure.symm

instance GapMixture.residual_finite {I : Type} [Fintype I] {μ : Measure Gap}
    [IsProbabilityMeasure μ] (M : GapMixture I μ) : IsFiniteMeasure M.residual :=
  isFiniteMeasure_of_le μ M.residual_le

theorem GapMixture.mass_balance {I : Type} [Fintype I] {μ : Measure Gap}
    [IsProbabilityMeasure μ] (M : GapMixture I μ) :
    M.residual.real Set.univ + ∑ i, (M.weight i : ℝ) = 1 := by
  have he : (1 : ℝ≥0∞) = M.residual Set.univ+∑ i, (M.weight i : ℝ≥0∞) := by
    calc
      _ = μ Set.univ := (measure_univ : μ Set.univ = 1).symm
      _ = (M.residual+∑ i, M.weight i • M.law i) Set.univ :=
        congrArg (fun η : Measure Gap => η Set.univ) M.eq_measure
      _ = _ := by
        rw [Measure.add_apply]
        simp only [Measure.finsetSum_apply,Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,
          measure_univ,mul_one]
  have h := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add (measure_ne_top _ _) (ENNReal.sum_ne_top.mpr (fun i _ => ENNReal.coe_ne_top)),
    ENNReal.toReal_sum (fun i _ => ENNReal.coe_ne_top)] at h
  simpa only [Measure.real,ENNReal.coe_toReal,ENNReal.toReal_one] using h.symm

theorem GapMixture.component_le {I : Type} [Fintype I] {μ : Measure Gap}
    (M : GapMixture I μ) (i : I) : M.weight i • M.law i ≤ μ := by
  calc
    _ ≤ ∑ j, M.weight j • M.law j :=
      Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ i)
    _ ≤ M.residual+∑ j, M.weight j • M.law j := Measure.le_add_left le_rfl
    _ = μ := M.eq_measure.symm

end ThresholdHC.AdditiveConfidence
