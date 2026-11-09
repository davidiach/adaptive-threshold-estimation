import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Tactic

/-! A common-uniform increasing coupling for bounded nonnegative laws.
The inverse includes CDF atoms, in particular mass at zero. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval
namespace ThresholdHC.ArbitraryLawAdaptation

def boundedQuantile (f : StieltjesFunction ℝ) (u : I) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ (u : ℝ) ≤ f x}

theorem boundedQuantile_properties (f : StieltjesFunction ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hfM : f M = 1) (u : I) :
    0 ≤ boundedQuantile f u ∧ boundedQuantile f u ≤ M ∧
      (u : ℝ) ≤ f (boundedQuantile f u) := by
  have hne : {x : ℝ | 0 ≤ x ∧ (u : ℝ) ≤ f x}.Nonempty :=
    ⟨M, hM, hfM.symm ▸ u.property.2⟩
  have hb : BddBelow {x : ℝ | 0 ≤ x ∧ (u : ℝ) ≤ f x} := ⟨0, fun _ hx => hx.1⟩
  refine ⟨le_csInf hne (fun _ hx => hx.1), csInf_le hb ⟨hM, hfM.symm ▸ u.property.2⟩, ?_⟩
  rw [← f.iInf_Ioi_eq (boundedQuantile f u)]
  apply le_ciInf
  intro r
  obtain ⟨x, hx, hxr⟩ := exists_lt_of_csInf_lt hne r.property
  exact hx.2.trans (f.mono hxr.le)

theorem boundedQuantile_le_iff (f : StieltjesFunction ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hfM : f M = 1) (u : I) (x : ℝ) :
    boundedQuantile f u ≤ x ↔ 0 ≤ x ∧ (u : ℝ) ≤ f x := by
  have hp := boundedQuantile_properties f hM hfM u
  constructor
  · intro h
    exact ⟨hp.1.trans h, hp.2.2.trans (f.mono h)⟩
  · intro h
    exact csInf_le (show BddBelow {x : ℝ | 0 ≤ x ∧ (u : ℝ) ≤ f x} from
      ⟨0, fun _ hx => hx.1⟩) h

theorem boundedQuantile_monotone (f : StieltjesFunction ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hfM : f M = 1) : Monotone (boundedQuantile f) := by
  intro u v huv
  have hp := boundedQuantile_properties f hM hfM v
  exact (boundedQuantile_le_iff f hM hfM u _).mpr
    ⟨hp.1, (show (u : ℝ) ≤ (v : ℝ) from huv).trans hp.2.2⟩

theorem measurable_boundedQuantile (f : StieltjesFunction ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hfM : f M = 1) : Measurable (boundedQuantile f) :=
  (boundedQuantile_monotone f hM hfM).measurable

theorem boundedQuantile_antitone_cdf (f g : StieltjesFunction ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hfM : f M = 1) (hgM : g M = 1)
    (hgf : ∀ x, g x ≤ f x) (u : I) : boundedQuantile f u ≤ boundedQuantile g u := by
  have hp := boundedQuantile_properties g hM hgM u
  exact (boundedQuantile_le_iff f hM hfM u _).mpr ⟨hp.1, hp.2.2.trans (hgf _)⟩

theorem boundedQuantile_map_volume (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hzero : μ (Iio 0) = 0) {M : ℝ} (hM : 0 ≤ M) (hμM : cdf μ M = 1) :
    (volume : Measure I).map (boundedQuantile (cdf μ)) = μ := by
  have hm := measurable_boundedQuantile (cdf μ) hM hμM
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply hm measurableSet_Iic]
  by_cases hx : 0 ≤ x
  · have he : boundedQuantile (cdf μ) ⁻¹' Iic x =
        Iic (⟨cdf μ x, cdf_nonneg μ x, cdf_le_one μ x⟩ : I) := by
      ext u
      simp only [Set.mem_preimage, Set.mem_Iic, boundedQuantile_le_iff (cdf μ) hM hμM, hx, true_and]
      rfl
    rw [he, unitInterval.volume_Iic, ofReal_cdf]
  · have he : boundedQuantile (cdf μ) ⁻¹' Iic x = ∅ := by
      ext u
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr (lt_of_lt_of_le (lt_of_not_ge hx) (boundedQuantile_properties (cdf μ) hM hμM u).1)
    rw [he, measure_empty]
    symm
    exact measure_mono_null (fun y hy => lt_of_le_of_lt hy (lt_of_not_ge hx)) hzero

def cdfCoupling (μ ν : Measure ℝ) : Measure (ℝ × ℝ) :=
  (volume : Measure I).map (fun u => (boundedQuantile (cdf μ) u, boundedQuantile (cdf ν) u))

theorem cdfCoupling_marginals (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ0 : μ (Iio 0) = 0) (hν0 : ν (Iio 0) = 0) {M : ℝ} (hM : 0 ≤ M)
    (hμM : cdf μ M = 1) (hνM : cdf ν M = 1) :
    (cdfCoupling μ ν).map Prod.fst = μ ∧ (cdfCoupling μ ν).map Prod.snd = ν := by
  have hm := (measurable_boundedQuantile (cdf μ) hM hμM).prodMk
    (measurable_boundedQuantile (cdf ν) hM hνM)
  constructor
  · rw [cdfCoupling, Measure.map_map measurable_fst hm]
    exact boundedQuantile_map_volume μ hμ0 hM hμM
  · rw [cdfCoupling, Measure.map_map measurable_snd hm]
    exact boundedQuantile_map_volume ν hν0 hM hνM

theorem cdfCoupling_increasing (μ ν : Measure ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hμM : cdf μ M = 1) (hνM : cdf ν M = 1) (hdom : ∀ x, cdf ν x ≤ cdf μ x) :
    ∀ᵐ z ∂cdfCoupling μ ν, z.1 ≤ z.2 := by
  have hm := (measurable_boundedQuantile (cdf μ) hM hμM).prodMk
    (measurable_boundedQuantile (cdf ν) hM hνM)
  rw [cdfCoupling, ae_map_iff hm.aemeasurable (measurableSet_le measurable_fst measurable_snd)]
  exact Filter.Eventually.of_forall (boundedQuantile_antitone_cdf _ _ hM hμM hνM hdom)

theorem exists_increasing_coupling_of_cdf (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ0 : μ (Iio 0) = 0) (hν0 : ν (Iio 0) = 0) {M : ℝ} (hM : 0 ≤ M)
    (hμM : cdf μ M = 1) (hνM : cdf ν M = 1) (hdom : ∀ x, cdf ν x ≤ cdf μ x) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧
      π.map Prod.snd = ν ∧ (∀ᵐ z ∂π, z.1 ≤ z.2) := by
  have hm := (measurable_boundedQuantile (cdf μ) hM hμM).prodMk
    (measurable_boundedQuantile (cdf ν) hM hνM)
  have hp : IsProbabilityMeasure (cdfCoupling μ ν) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  exact ⟨cdfCoupling μ ν, hp, (cdfCoupling_marginals μ ν hμ0 hν0 hM hμM hνM).1,
    (cdfCoupling_marginals μ ν hμ0 hν0 hM hμM hνM).2,
    cdfCoupling_increasing μ ν hM hμM hνM hdom⟩

end ThresholdHC.ArbitraryLawAdaptation
