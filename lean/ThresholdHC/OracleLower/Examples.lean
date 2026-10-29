import ThresholdHC.OracleLower.SelectedSemantics

noncomputable section
open MeasureTheory
namespace ThresholdHC.OracleLower

/-- Create two coins, choosing the second magnitude from the first flip;
then revisit the first coin and stop. Birth times are observation indices. -/
def feedbackExample : SelectedEstimator Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  request := fun _ xs => if xs.length < 2 then some none else
    if xs.length = 2 then some (some 0) else none
  request_measurable := fun _ => measurable_const
  newGap := fun _ xs => if xs.headD false then ⟨1/8,by norm_num,by norm_num⟩
    else ⟨1/2,by norm_num,le_rfl⟩
  newGap_measurable := fun _ => measurable_const
  reuse_valid := by
    intro r xs j h
    split_ifs at h with hlen htwo
    · simp at h
    · have hj : j = 0 := by simpa using h.symm
      subst j
      simp [htwo]
  output := fun _ => 0
  output_measurable := measurable_const

theorem feedbackExample_selects_and_revisits :
    feedbackExample.request () [] = some none ∧
    feedbackExample.request () [true] = some none ∧
    (selectedOracle feedbackExample).gap () (Encodable.encode [true]) ≠
      (selectedOracle feedbackExample).gap () (Encodable.encode [false]) ∧
    (selectedOracle feedbackExample).policy () [true,false] =
      (selectedOracle feedbackExample).policy () [] := by
  norm_num [selectedOracle,selectedLabel,feedbackExample]

end ThresholdHC.OracleLower
