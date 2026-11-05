import ThresholdHC.LawAdaptation.Identification

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.LawAdaptation

/-- On correct identification, the selected procedure is the true-law procedure.
There is no union over the candidate laws and no conditional-error assumption. -/
theorem selected_failure_bound {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (chosen : Ω → ι) (truth : ι) (good : ι → Ω → Prop)
    {δpilot δoracle : ℝ≥0∞}
    (hp : P {ω | chosen ω ≠ truth} ≤ δpilot)
    (ho : P {ω | ¬ good truth ω} ≤ δoracle) :
    P {ω | ¬ good (chosen ω) ω} ≤ δpilot + δoracle := by
  calc
    _ ≤ P ({ω | chosen ω ≠ truth} ∪ {ω | ¬ good truth ω}) := by
      apply measure_mono
      intro ω hω
      by_cases he : chosen ω = truth
      · exact Or.inr (by simpa only [Set.mem_ofPred_eq, he] using hω)
      · exact Or.inl he
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add hp ho)

/-- Uniform-in-budget coverage and width transfer on the same good event. -/
theorem selected_simultaneous {Ω ι T : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (chosen : Ω → ι) (truth : ι) (property : ι → T → Ω → Prop)
    {δpilot δoracle : ℝ≥0∞}
    (hp : P {ω | chosen ω ≠ truth} ≤ δpilot)
    (ho : P {ω | ¬ ∀ t, property truth t ω} ≤ δoracle) :
    P {ω | ¬ ∀ t, property (chosen ω) t ω} ≤ δpilot + δoracle :=
  selected_failure_bound P chosen truth (fun i ω => ∀ t, property i t ω) hp ho

/-- A deterministic paid pilot followed by a pathwise capped procedure
stays within the original physical budget. -/
theorem paid_pilot_cap (H B flips : ℕ) (h : flips ≤ B-H) :
    min H B + flips ≤ B := by omega

end ThresholdHC.LawAdaptation

