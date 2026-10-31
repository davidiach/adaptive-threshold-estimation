import ThresholdHC.StoppingProgram.Perspective
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! The second moment of a finite-observation posterior score is the sum
of its closed cell perspectives. Null cells are included exactly. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.StoppingProgram

theorem finite_posterior_secondMoment {Ω W : Type*} [mΩ : MeasurableSpace Ω]
    [mW : MeasurableSpace W] [MeasurableSingletonClass W] [Fintype W]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → W) (hX : Measurable X)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    (∫⁻ x, ENNReal.ofReal (((μ[f | (inferInstance : MeasurableSpace W).comap X]) x)^2) ∂μ) =
      ∑ w : W, perspective (∫ x in X ⁻¹' {w}, f x ∂μ) (μ.real (X ⁻¹' {w})) := by
  let m := mW.comap X
  letI : MeasurableSpace Ω := mΩ
  have hm : m ≤ mΩ := hX.comap_le
  obtain ⟨g,hg,he⟩ := (stronglyMeasurable_condExp (μ := μ) (f := f) (m := m)).exists_eq_measurable_comp
  have hcell (w : W) : MeasurableSet[m] (X ⁻¹' {w}) := ⟨{w},measurableSet_singleton w,rfl⟩
  have hnum (w : W) : (∫ x in X ⁻¹' {w}, f x ∂μ) = μ.real (X ⁻¹' {w})*g w := by
    rw [←setIntegral_condExp hm hf (hcell w)]
    have hc : (∫ x in X ⁻¹' {w}, (μ[f | m]) x ∂μ) = ∫ _ in X ⁻¹' {w}, g w ∂μ := by
      apply setIntegral_congr_fun (hX (measurableSet_singleton w))
      intro x hx
      rw [he]
      change g (X x) = g w
      exact congrArg g hx
    rw [hc]
    simp [measureReal_def]
  change (∫⁻ x, ENNReal.ofReal (((μ[f | m]) x)^2) ∂μ) = _
  rw [he]
  change (∫⁻ x, ENNReal.ofReal ((g (X x))^2) ∂μ) = _
  rw [←lintegral_map ((hg.measurable.pow_const 2).ennreal_ofReal) hX,lintegral_fintype]
  apply Finset.sum_congr rfl
  intro w _
  rw [Measure.map_apply hX (measurableSet_singleton w)]
  symm
  calc
    _ = perspective (μ.real (X ⁻¹' {w})*g w) (μ.real (X ⁻¹' {w})*1) := by rw [hnum,mul_one]
    _ = ENNReal.ofReal (μ.real (X ⁻¹' {w}))*perspective (g w) 1 :=
      perspective_scale _ _ ENNReal.toReal_nonneg
    _ = _ := by
      rw [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top μ _)]
      simp [perspective,mul_comm]

end ThresholdHC.Genie
