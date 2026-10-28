import ThresholdHC.Tier6.TestingFinite
import ThresholdHC.Proofs.Constants

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.Confidence
open ThresholdHC.Tier6

theorem klDiv_confidence_separation {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (s : Set Ω) (hs : MeasurableSet s) (δ : ℝ)
    (hδ : 0 < δ) (hδle : δ ≤ 1/4)
    (hP : 1-δ ≤ P.real s) (hQ : Q.real s ≤ δ) :
    ENNReal.ofReal (Real.log (1/δ)/4) ≤ klDiv P Q := by
  classical
  by_cases htop : klDiv P Q = ∞
  · simp [htop]
  have hac := (klDiv_ne_top_iff.mp htop).1
  have hQpos : 0 < Q s := by
    by_contra hn
    have hzero : Q s = 0 := le_antisymm (not_lt.mp hn) bot_le
    have hpzero : P.real s = 0 := (measureReal_eq_zero_iff).mpr (hac hzero)
    linarith
  have hQcpos : 0 < Q sᶜ := by
    have hc : 0 < Q.real sᶜ := by rw [probReal_compl_eq_one_sub hs]; linarith
    exact (ENNReal.toReal_pos_iff.mp hc).1
  let test : Ω → Bool := fun x => decide (x ∈ s)
  have htrue : test ⁻¹' {true} = s := by ext x; simp [test]
  have hfalse : test ⁻¹' {false} = sᶜ := by ext x; simp [test]
  have htest : Measurable test := by
    apply measurable_to_bool
    rw [htrue]
    exact hs
  have hmapQ (b : Bool) : 0 < (Q.map test) {b} := by
    rw [Measure.map_apply htest (measurableSet_singleton b)]
    cases b
    · simpa [hfalse] using hQcpos
    · simpa [htrue] using hQpos
  have hid := klDiv_finite_of_positive (P.map test) (Q.map test) hmapQ
  have hmap (M : Measure Ω) (b : Bool) :
      (M.map test).real {b} = if b then M.real s else M.real sᶜ := by
    rw [map_measureReal_apply htest (measurableSet_singleton b)]
    cases b <;> simp [htrue, hfalse]
  have hkl : klDiv (P.map test) (Q.map test) = ENNReal.ofReal (klB (P.real s) (Q.real s)) := by
    rw [hid]
    simp only [Fintype.sum_bool, hmap, Bool.false_eq_true, ↓reduceIte]
    rw [probReal_compl_eq_one_sub hs, probReal_compl_eq_one_sub hs]
    congr 1
  have hsep := Proofs.Tier2Information.kl_test_separation δ (P.real s) (Q.real s)
    hδ (by linarith) measureReal_nonneg measureReal_le_one
    (ENNReal.toReal_pos (ne_of_gt hQpos) (measure_ne_top Q _)) hQ hP
  have hbin := Proofs.kl_delta_lower δ hδ hδle
  rw [← Proofs.kl_delta_identity δ hδ (by linarith)] at hbin
  have hb : Real.log (1/δ)/4 ≤ klB (P.real s) (Q.real s) := by linarith
  calc
    ENNReal.ofReal (Real.log (1/δ)/4) ≤ ENNReal.ofReal (klB (P.real s) (Q.real s)) :=
      ENNReal.ofReal_le_ofReal hb
    _ = klDiv (P.map test) (Q.map test) := hkl.symm
    _ ≤ klDiv P Q := klDiv_map_le P Q htest

end ThresholdHC.Confidence
