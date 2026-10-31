import ThresholdHC.StoppingProgram.MixtureStatistics

/-! Removing null-rate tables gives a nonempty finite positive-rate family
when the root intensity is positive. -/

noncomputable section
open scoped BigOperators Classical
namespace ThresholdHC.StoppingProgram

abbrev PositiveTable {N : ℕ} (f : Flow N) := {b : CountState N → Bool // 0 < flowTableRate f b}

theorem positiveTable_nonempty {N : ℕ} (f : Flow N) (hf : FlowCone f) (hr : 0 < intensity f) :
    Nonempty (PositiveTable f) := by
  by_contra h
  have hz (b : CountState N → Bool) : flowTableRate f b = 0 := by
    have hn : ¬0 < flowTableRate f b := fun hb => h ⟨⟨b,hb⟩⟩
    linarith [flowTableRate_nonneg f hf b]
  have hs := flowTableRate_sum f
  simp only [hz,Finset.sum_const_zero] at hs
  linarith

theorem positiveTable_enumeration {N : ℕ} (f : Flow N) (hf : FlowCone f) (hr : 0 < intensity f) :
    ∃ J : ℕ, Nonempty (Fin (J+1) ≃ PositiveTable f) := by
  letI : Nonempty (PositiveTable f) := positiveTable_nonempty f hf hr
  have hc : 0 < Fintype.card (PositiveTable f) := Fintype.card_pos
  obtain ⟨J,hJ⟩ := Nat.exists_eq_succ_of_ne_zero hc.ne'
  exact ⟨J,⟨(finCongr hJ.symm).trans (Fintype.equivFin (PositiveTable f)).symm⟩⟩

theorem positiveTable_sum {N : ℕ} (f : Flow N) (hf : FlowCone f) (H : (CountState N → Bool) → ℝ) :
    (∑ b : PositiveTable f, flowTableRate f b.val*H b.val) =
      ∑ b : CountState N → Bool, flowTableRate f b*H b := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun b => 0 < flowTableRate f b) (fun b => flowTableRate f b*H b)
  have hz : (∑ b : {b : CountState N → Bool // ¬0 < flowTableRate f b}, flowTableRate f b.val*H b.val) = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    have hb : flowTableRate f b.val = 0 := by
      have hp := b.property
      linarith [flowTableRate_nonneg f hf b.val]
    rw [hb,zero_mul]
  rw [hz,add_zero] at h
  exact h

theorem enumeratedTable_sum {N J : ℕ} (f : Flow N) (hf : FlowCone f) (e : Fin (J+1) ≃ PositiveTable f)
    (H : (CountState N → Bool) → ℝ) :
    (∑ i : Fin (J+1), flowTableRate f (e i).val*H (e i).val) =
      ∑ b : CountState N → Bool, flowTableRate f b*H b := by
  rw [e.sum_comp (fun b => flowTableRate f b.val*H b.val)]
  exact positiveTable_sum f hf H

end ThresholdHC.StoppingProgram
