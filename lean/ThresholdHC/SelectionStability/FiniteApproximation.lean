import ThresholdHC.SelectionStability.Grid
import ThresholdHC.SelectionStability.Approximation

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace ThresholdHC.SelectionStability
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

/-- Move at most η mass above a positive lower cutoff. The error is measured in probability TV. -/
theorem trim_small_gaps (μ : Measure Gap) [IsProbabilityMeasure μ] {η : ℝ} (hη : 0 < η) :
    ∃ (t : Gap) (ν : Measure Gap), IsProbabilityMeasure ν ∧ Ici t ∈ ae ν ∧ tvDist μ ν / 2 ≤ η := by
  let p := min η 1
  have hp : 0 < p := lt_min hη zero_lt_one
  have hp₁ : p ≤ 1 := min_le_right _ _
  have hq := EntropyTailQuantile.quantileThreshold_properties μ hp hp₁
  let t : Gap := ⟨EntropyTailQuantile.quantileThreshold μ p, hq.1, hq.2.1⟩
  let s := Ici t
  let core := μ.restrict s
  let ν := core + μ sᶜ • Measure.dirac t
  have hs : MeasurableSet s := measurableSet_Ici
  have hm : μ.real sᶜ ≤ η := by
    have h := EntropyTailQuantile.quantileThreshold_mass_below μ hp hp₁
    have he : sᶜ = {d : Gap | (d:ℝ) < EntropyTailQuantile.quantileThreshold μ p} := by
      ext d
      change (¬ (t:ℝ) ≤ (d:ℝ)) ↔ (d:ℝ) < (t:ℝ)
      exact not_le
    rw [he]
    exact h.trans (min_le_left η 1)
  have hprob : IsProbabilityMeasure ν := by
    constructor
    change (core + μ sᶜ • Measure.dirac t) univ = 1
    simp [core, Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_add_measure_compl hs]
  have : IsProbabilityMeasure ν := hprob
  have hcore : core ≤ ν := Measure.le_add_right le_rfl
  have ht : tvDist μ ν ≤ (1-μ.real s)+(1-μ.real s) := by
    have h := tvDist_triangle μ core ν
    rwa [tvDist_of_ge (show core ≤ μ from Measure.restrict_le_self),tvDist_of_le hcore,
      probReal_univ (μ := μ),probReal_univ (μ := ν),
      show core.real univ = μ.real s from measureReal_restrict_apply_univ _] at h
  refine ⟨t,ν,hprob,?_,?_⟩
  · change ∀ᵐ x ∂(core + μ sᶜ • Measure.dirac t), x ∈ s
    rw [ae_add_measure_iff]
    refine ⟨ae_restrict_mem hs, ?_⟩
    apply Measure.ae_smul_measure
    simp [s]
  · rw [probReal_compl_eq_one_sub hs] at hm
    linarith

/-- For every prescribed positive TV tolerance and every distortion above one, the premises
of the enclosure theorem can be realized with a finitely supported pushforward. -/
theorem finite_approximation_exists (μ : Measure Gap) [IsProbabilityMeasure μ] {η r : ℝ}
    (hη : 0 < η) (hr : 1 < r) :
    ∃ (ν : Measure Gap) (T : Gap → Gap), IsProbabilityMeasure ν ∧ Measurable T ∧
      tvDist μ ν / 2 ≤ η ∧ (∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ)) ∧
      (∀ j, T ⁻¹' band j = band j) ∧ (ν.map T).support.Finite := by
  obtain ⟨t,ν,hν,hcore,hTV⟩ := trim_small_gaps μ hη
  obtain ⟨T,hm,hd,hb,hF⟩ := finite_rounding_grid t hr
  refine ⟨ν,T,hν,hm,hTV,hd,hb,hF.subset (Measure.support_subset_of_isClosed hF.isClosed ?_)⟩
  rw [mem_ae_map_iff hm.aemeasurable hF.measurableSet]
  filter_upwards [show ∀ᵐ x ∂ν, x ∈ Ici t from hcore] with x hx
  exact mem_image_of_mem T hx

end ThresholdHC.SelectionStability
