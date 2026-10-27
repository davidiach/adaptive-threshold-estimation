import ThresholdHC.Tier4.FiniteDensity
import ThresholdHC.Proofs.Tier2.InformationCore
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.Tier6

theorem klDiv_finite_of_positive {A : Type} [MeasurableSpace A] [Fintype A]
    [MeasurableSingletonClass A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hQ : ∀ a, 0 < Q {a}) :
    klDiv P Q = ENNReal.ofReal (∑ a, P.real {a} * Real.log (P.real {a} / Q.real {a})) := by
  let r : A → ℝ := fun a => P.real {a} / Q.real {a}
  have hr0 (a : A) : 0 ≤ r a := div_nonneg (measureReal_nonneg) (measureReal_nonneg)
  have hd : Q.withDensity (fun a => ENNReal.ofReal (r a)) = P := by
    apply Measure.ext_of_singleton
    intro a
    rw [withDensity_apply _ (measurableSet_singleton a), lintegral_singleton]
    dsimp [r, measureReal_def]
    rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos (ne_of_gt (hQ a)) (measure_ne_top Q _))]
    rw [ENNReal.ofReal_toReal (measure_ne_top P _), ENNReal.ofReal_toReal (measure_ne_top Q _)]
    exact ENNReal.div_mul_cancel (ne_of_gt (hQ a)) (measure_ne_top Q _)
  rw [Tier4.klDiv_of_finite_likelihood P Q id measurable_id r hr0 hd]
  congr 1
  rw [integral_fintype (Integrable.of_finite)]
  simp [r, smul_eq_mul]

theorem klDiv_event_separation {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (s : Set Ω) (hs : MeasurableSet s)
    (hP : (3/4:ℝ) ≤ P.real s) (hQ : Q.real s ≤ 1/4) :
    ENNReal.ofReal (1/2:ℝ) ≤ klDiv P Q := by
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
  have hsep := Proofs.Tier2Information.kl_test_separation (1/4) (P.real s) (Q.real s)
    (by norm_num) (by norm_num) measureReal_nonneg (measureReal_le_one)
    (ENNReal.toReal_pos (ne_of_gt hQpos) (measure_ne_top Q _)) hQ (by linarith)
  have hbin := Proofs.Tier2Information.binary_pinsker (3/4) (1/4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : (1/2:ℝ) ≤ klB (P.real s) (Q.real s) := by norm_num at hbin hsep ⊢; linarith
  calc
    ENNReal.ofReal (1/2:ℝ) ≤ ENNReal.ofReal (klB (P.real s) (Q.real s)) := ENNReal.ofReal_le_ofReal hb
    _ = klDiv (P.map test) (Q.map test) := hkl.symm
    _ ≤ klDiv P Q := klDiv_map_le P Q htest

end ThresholdHC.Tier6
