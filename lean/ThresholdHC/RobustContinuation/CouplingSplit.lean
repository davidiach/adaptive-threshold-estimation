import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Splitting a measure along a decomposition of its image.

If the image of a measure `π` under a measurable map `p` is a sum
`ν₁ + ν₂` of finite measures, then `π` is a sum `π₁ + π₂` with images `ν₁`
and `ν₂`. The parts are `π` weighted by a density of `ν₁` in `ν₁ + ν₂`,
read at the image point, and by its complement.

A coupling of reference gaps and true gaps is split in this way along the
design of the reference law: selected core, resolved tail and unresolved
part. Each part of the coupling inherits every almost-sure property of the
coupling, such as `z.1 ≤ z.2`. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ThresholdHC.RobustContinuation

variable {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]

/-- Weighting by a function of the image point, then taking the image, is
the image weighted by that function. -/
theorem map_withDensity_comp (π : Measure α) {p : α → γ} (hp : Measurable p)
    {g : γ → ℝ≥0∞} (hg : Measurable g) :
    (π.withDensity (g ∘ p)).map p = (π.map p).withDensity g := by
  ext E hE
  rw [Measure.map_apply hp hE, withDensity_apply _ (hp hE), withDensity_apply _ hE,
    setLIntegral_map hE hg hp]
  rfl

/-- A measure whose image is `ν₁ + ν₂` is a sum of two measures with
images `ν₁` and `ν₂`. -/
theorem exists_split_of_map_add (π : Measure α) {p : α → γ} (hp : Measurable p)
    (ν₁ ν₂ : Measure γ) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] (h : π.map p = ν₁ + ν₂) :
    ∃ π₁ π₂ : Measure α, π₁ + π₂ = π ∧ π₁.map p = ν₁ ∧ π₂.map p = ν₂ := by
  let f := ν₁.rnDeriv (ν₁ + ν₂)
  let g : γ → ℝ≥0∞ := fun x => min (f x) 1
  have hf : Measurable f := Measure.measurable_rnDeriv _ _
  have hg : Measurable g := hf.min measurable_const
  have hg' : Measurable (fun x => 1 - g x) := measurable_const.sub hg
  have hle : ν₁ ≤ ν₁ + ν₂ := Measure.le_add_right le_rfl
  have hfg : g =ᵐ[ν₁ + ν₂] f := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hle] with x hx
    exact min_eq_left hx
  have h1 : (ν₁ + ν₂).withDensity g = ν₁ := by
    rw [withDensity_congr_ae hfg]
    exact Measure.withDensity_rnDeriv_eq ν₁ (ν₁ + ν₂) (Measure.absolutelyContinuous_of_le hle)
  have hsum : g + (fun x => 1 - g x) = 1 := by
    funext x
    exact add_tsub_cancel_of_le (min_le_right _ _)
  have h2 : (ν₁ + ν₂).withDensity (fun x => 1 - g x) = ν₂ := by
    have hadd : (ν₁ + ν₂).withDensity g + (ν₁ + ν₂).withDensity (fun x => 1 - g x) = ν₁ + ν₂ := by
      rw [← withDensity_add_left hg, hsum, withDensity_one]
    rw [h1] at hadd
    exact (Measure.add_right_inj ν₁ _ _).mp hadd
  refine ⟨π.withDensity (g ∘ p), π.withDensity ((fun x => 1 - g x) ∘ p), ?_, ?_, ?_⟩
  · rw [← withDensity_add_left (hg.comp hp)]
    have hcomp : g ∘ p + (fun x => 1 - g x) ∘ p = 1 := by
      funext x
      exact congrFun hsum (p x)
    rw [hcomp, withDensity_one]
  · rw [map_withDensity_comp π hp hg, h, h1]
  · rw [map_withDensity_comp π hp hg', h, h2]

/-- The same for a sum of three measures. -/
theorem exists_split_of_map_add₃ (π : Measure α) {p : α → γ} (hp : Measurable p)
    (ν₁ ν₂ ν₃ : Measure γ) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] [IsFiniteMeasure ν₃]
    (h : π.map p = ν₁ + ν₂ + ν₃) :
    ∃ π₁ π₂ π₃ : Measure α, π₁ + π₂ + π₃ = π ∧ π₁.map p = ν₁ ∧ π₂.map p = ν₂ ∧
      π₃.map p = ν₃ := by
  obtain ⟨π₁₂, π₃, hπ, h12, h3⟩ := exists_split_of_map_add π hp (ν₁ + ν₂) ν₃ h
  obtain ⟨π₁, π₂, hπ', h1, h2⟩ := exists_split_of_map_add π₁₂ hp ν₁ ν₂ h12
  exact ⟨π₁, π₂, π₃, by rw [hπ', hπ], h1, h2, h3⟩

end ThresholdHC.RobustContinuation
