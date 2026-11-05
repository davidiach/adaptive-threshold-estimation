
import ThresholdHC.AnytimeLower.TailFamily

noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier6

theorem tailDropIndex_strictMono (μ : Measure Gap) [IsFiniteMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ}) :
    StrictMono (tailDropIndex μ hτ hμ) :=
  dropIndex_strictMono (tailMassSequence μ τ) (tailMassSequence_pos μ hτ hμ)
    (tailMassSequence_tendsto_zero μ hτ)

theorem selectedScale_tendsto_zero (μ : Measure Gap) [IsFiniteMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ}) :
    Tendsto (selectedScale μ hτ hμ) atTop (𝓝 0) :=
  (geometricScale_tendsto_zero τ).comp (tailDropIndex_strictMono μ hτ hμ).tendsto_atTop

theorem tailMassSequence_quarter (μ : Measure Gap) [IsFiniteMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) (j : ℕ) :
    tailMassSequence μ τ j/4 ≤ tailMassSequence μ τ (j+1) := by
  have he : geometricScale τ (j+1) = geometricScale τ j/4 := by
    unfold geometricScale
    rw [pow_succ]
    ring
  unfold tailMassSequence
  rw [he]
  exact profileMass_quarter μ τ (geometricScale_pos hτ j).le

theorem tailMassSequence_plateau (μ : Measure Gap) [IsFiniteMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ})
    (k j : ℕ) (hl : tailDropIndex μ hτ hμ k ≤ j)
    (hu : j < tailDropIndex μ hτ hμ (k+1)) :
    tailMassSequence μ τ (tailDropIndex μ hτ hμ k)/4 < tailMassSequence μ τ j :=
  before_nextDrop (tailMassSequence μ τ) (tailMassSequence_pos μ hτ hμ)
    (tailMassSequence_tendsto_zero μ hτ) hl hu

theorem tailMassSequence_overshoot (μ : Measure Gap) [IsFiniteMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ}) (k : ℕ) :
    tailMassSequence μ τ (tailDropIndex μ hτ hμ k)/16 <
      tailMassSequence μ τ (tailDropIndex μ hτ hμ (k+1)) :=
  nextDrop_overshoot (tailMassSequence μ τ) (tailMassSequence_pos μ hτ hμ)
    (tailMassSequence_tendsto_zero μ hτ) (tailMassSequence_quarter μ hτ) _

end ThresholdHC.AnytimeLower
