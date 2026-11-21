import ThresholdHC.RevisitUpper.Specification
import ThresholdHC.LargeBudgetRMS.RevisitPolicy

/-! The library reader `SharpRMS.Revisit.label` satisfies the 20+5 labelling
rule of the specification. -/
namespace ThresholdHC.RevisitUpper
open ThresholdHC.SharpRMS.Revisit

/-- After a complete pilot word, the label is the follow-up label at the
number of follow-up answers. -/
theorem label_append (v w : List Bool) (hv : v.length = 20) :
    label (v ++ w) = follow v w.length := by
  have take : (v ++ w).take 20 = v := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  simp [label, hv, take]

theorem label_rule : RevisitRule label := by
  refine ⟨fun xs h => by simp [label, h], fun v w hv hw => ?_, fun v w w' hv _ _ e => ?_⟩
  · rw [label_append v w hv]
    rcases follow_mode v hv w.length hw with ⟨md, fresh⟩ | ⟨b, md, old, bit⟩
    · refine ⟨fun H => ?_, fun T => ?_, fun _ _ => fresh⟩
      · unfold mode at md
        rw [ite_eq_left H] at md
        cases md
      · unfold mode at md
        rw [ite_eq_right (by omega), ite_eq_left T] at md
        cases md
    · refine ⟨fun H => ?_, fun T => ?_, fun nH nT => ?_⟩
      · unfold mode at md
        rw [ite_eq_left H] at md
        obtain rfl : true = b := Option.some.inj md
        exact ⟨old, bit⟩
      · unfold mode at md
        rw [ite_eq_right (by omega), ite_eq_left T] at md
        obtain rfl : false = b := Option.some.inj md
        exact ⟨old, bit⟩
      · unfold mode at md
        rw [ite_eq_right nH, ite_eq_right nT] at md
        cases md
  · rw [label_append v w hv, label_append v w' hv] at e
    exact follow_inj v e

end ThresholdHC.RevisitUpper
