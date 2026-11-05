import ThresholdHC.ObservableSimulation.OriginalExperiment

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ThresholdHC.ObservedState
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation

/-- Independent sign-symmetric noise turns a larger-gap observation into a
smaller-gap observation while retaining the same hidden cell sign. -/
def noiseRate (b d : Gap) (hd : (d : ℝ) ≤ b) : unitInterval :=
  ⟨(1 - (d : ℝ) / b) / 2, by
    have hratio : 0 ≤ (d : ℝ) / b := div_nonneg d.property.1.le b.property.1.le
    have hu : (d : ℝ) / b ≤ 1 := (div_le_one b.property.1).mpr hd
    constructor <;> linarith⟩

theorem garbled_parameter (b d : Gap) (hd : (d : ℝ) ≤ b) (s : Bool) :
    (gapParameter s b : ℝ) * (1 - noiseRate b d hd) +
      (1 - (gapParameter s b : ℝ)) * noiseRate b d hd = (gapParameter s d : ℝ) := by
  have hb : (b : ℝ) ≠ 0 := ne_of_gt b.property.1
  cases s <;> dsimp [gapParameter,noiseRate]
  all_goals field_simp [hb]
  all_goals ring

theorem garbling_law (b d : Gap) (hd : (d : ℝ) ≤ b) (s : Bool) :
    ((bernoulliMeasure true false (gapParameter s b)).prod
      (bernoulliMeasure true false (noiseRate b d hd))).map (fun z => Bool.xor z.1 z.2) =
        bernoulliMeasure true false (gapParameter s d) := by
  apply measure_eq_of_bounded_real_tests
  intro F hF _
  rw [integral_map (measurable_of_countable (fun z : Bool × Bool => Bool.xor z.1 z.2)).aemeasurable
    hF.aestronglyMeasurable]
  rw [integral_prod _ (Integrable.of_finite)]
  simp only [integral_bernoulliMeasure,smul_eq_mul]
  simp only [Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false]
  have h := garbled_parameter b d hd s
  linear_combination (F true - F false) * h

end ThresholdHC.ObservedState
