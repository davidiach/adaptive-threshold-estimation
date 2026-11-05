import ThresholdHC.ObservedState.OuterMeasure

noncomputable section
open MeasureTheory Set
namespace ThresholdHC.ObservedState
open ThresholdHC.Tier6

/-- Every finite-range gap map has a finite measurable cell labeling with
an exact pointwise reconstruction of its magnitude. -/
theorem finite_range_labels (T : Gap → Gap) (hm : Measurable T) (hF : (range T).Finite) :
    ∃ N : ℕ, 0 < N ∧ ∃ (cap : Fin N → Gap) (label : Gap → Fin N),
      Measurable label ∧ ∀ d, cap (label d) = T d := by
  classical
  let I := range T
  let : Fintype I := hF.fintype
  have : Nonempty I := ⟨⟨T ⟨1 / 2,by norm_num⟩,mem_range_self _⟩⟩
  let e := Fintype.equivFin I
  let cell (d : Gap) : I := ⟨T d,mem_range_self d⟩
  have hc : Measurable cell := hm.subtype_mk
  refine ⟨Fintype.card I,Fintype.card_pos,fun i => (e.symm i).val,e ∘ cell,
    (measurable_of_countable e).comp hc,?_⟩
  intro d
  simp [cell]

def labelWeight {N : ℕ} (μ : Measure Gap) (label : Gap → Fin N) (i : Fin N) : ℝ :=
  (μ.map label).real {i}

theorem labelWeight_nonneg {N : ℕ} (μ : Measure Gap) (label : Gap → Fin N) (i : Fin N) :
    0 ≤ labelWeight μ label i := measureReal_nonneg

theorem labelWeight_sum {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (label : Gap → Fin N) (hm : Measurable label) :
    (∑ i, labelWeight μ label i) = 1 := by
  have : IsProbabilityMeasure (μ.map label) := (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  simpa only [labelWeight,Finset.coe_univ,probReal_univ] using
    sum_measureReal_singleton (μ := μ.map label) Finset.univ

theorem label_moment {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (label : Gap → Fin N) (hm : Measurable label) (cap : Fin N → Gap) (F : Gap → ℝ) :
    (∫ d, F (cap (label d)) ∂μ) = ∑ i, labelWeight μ label i * F (cap i) := by
  have : IsProbabilityMeasure (μ.map label) := (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  rw [← integral_map (φ := label) (f := fun i => F (cap i)) hm.aemeasurable
    (measurable_of_countable (fun i => F (cap i))).aestronglyMeasurable,
    integral_fintype (Integrable.of_finite)]
  rfl

end ThresholdHC.ObservedState
