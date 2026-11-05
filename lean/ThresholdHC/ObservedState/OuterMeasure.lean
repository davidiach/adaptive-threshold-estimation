import ThresholdHC.ObservedState.Replication
import ThresholdHC.ObservedState.Rounding
import Mathlib.Probability.Kernel.Representation

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.ObservedState
open ThresholdHC.Tier6

def repetitionLaw (M : ℕ) : Measure (Fin M) := Measure.uniformOfFinset Finset.univ

instance repetitionLaw_probability (M : ℕ) [NeZero M] : IsProbabilityMeasure (repetitionLaw M) where
  measure_univ := by
    classical
    simp [repetitionLaw,Measure.uniformOfFinset_apply]
    exact ENNReal.div_self (a := (M : ℝ≥0∞)) (by exact_mod_cast NeZero.ne M) (by simp)

theorem repetitionLaw_singleton (M : ℕ) (k : Fin M) :
    (repetitionLaw M).real {k} = 1 / (M : ℝ) := by
  simp [repetitionLaw,measureReal_def]

/-- A uniform observed state can realize any prescribed gap law together
with an independent finite replication index. -/
theorem outer_source (μ : Measure Gap) [IsProbabilityMeasure μ] (M : ℕ) [NeZero M] :
    ∃ f : unitInterval → Gap × Fin M, Measurable f ∧
      volume.map f = μ.prod (repetitionLaw M) := by
  have : Nonempty Gap := ⟨⟨1 / 2,by norm_num⟩⟩
  have : StandardBorelSpace Gap := (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) (1 / 2))).standardBorel
  exact (μ.prod (repetitionLaw M)).exists_measurable_map_eq

/-- The uniform source produces the specified gap law exactly. -/
theorem outer_gap_law (μ : Measure Gap) [IsProbabilityMeasure μ] (M : ℕ) [NeZero M]
    (f : unitInterval → Gap × Fin M) (hf : Measurable f)
    (hl : volume.map f = μ.prod (repetitionLaw M)) :
    volume.map (fun u => (f u).1) = μ := by
  change volume.map (Prod.fst ∘ f) = _
  rw [← Measure.map_map measurable_fst hf,hl,Measure.map_fst_prod]
  simp

theorem finite_cell_law (μ : Measure Gap) [IsProbabilityMeasure μ] (M : ℕ) [NeZero M]
    {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (cell : Gap → I) (hc : Measurable cell)
    (f : unitInterval → Gap × Fin M) (hf : Measurable f)
    (hl : volume.map f = μ.prod (repetitionLaw M)) :
    volume.map (fun u => (cell (f u).1,(f u).2)) =
      (μ.map cell).prod (repetitionLaw M) := by
  have hm : Measurable (Prod.map cell (id : Fin M → Fin M)) := hc.prodMap measurable_id
  change volume.map (Prod.map cell id ∘ f) = _
  rw [← Measure.map_map hm hf,hl,← Measure.map_prod_map μ (repetitionLaw M) hc measurable_id,Measure.map_id]

theorem cell_mass (μ : Measure Gap) [IsProbabilityMeasure μ] (M : ℕ) [NeZero M]
    {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (cell : Gap → I) (hc : Measurable cell)
    (f : unitInterval → Gap × Fin M) (hf : Measurable f)
    (hl : volume.map f = μ.prod (repetitionLaw M)) (i : I) (k : Fin M) :
    volume.real {u : unitInterval | cell (f u).1 = i ∧ (f u).2 = k} =
      (μ.map cell).real {i} / M := by
  have hm : Measurable (fun u => (cell (f u).1,(f u).2)) := (hc.comp hf.fst).prodMk hf.snd
  have h := finite_cell_law μ M cell hc f hf hl
  have hh := congrArg (fun ν : Measure (I × Fin M) => ν.real {(i,k)}) h
  rw [map_measureReal_apply hm (measurableSet_singleton (i,k))] at hh
  have he : (fun u => (cell (f u).1,(f u).2)) ⁻¹' {(i,k)} =
      {u | cell (f u).1 = i ∧ (f u).2 = k} := by ext u; simp
  rw [he] at hh
  rw [hh]
  rw [← singleton_prod_singleton,measureReal_prod_prod,repetitionLaw_singleton]
  ring

end ThresholdHC.ObservedState
