import ThresholdHC.CriticalEntropy.FiniteGap

/-! A one-gap cost floor using only deterministic prefixes. -/

noncomputable section
open MeasureTheory InformationTheory Real
open scoped ENNReal
namespace ThresholdHC.CriticalAllSizes
open CriticalEntropy

theorem moderate_event_probability {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (s : Set Ω) (hs : MeasurableSet s)
    (hkl : klDiv P Q ≤ ENNReal.ofReal (8/15 : ℝ))
    (hQ : Q.real s ≤ 1/10) : P.real s ≤ 5/8 := by
  by_contra hn
  have hp : (5/8 : ℝ) ≤ P.real s := (lt_of_not_ge hn).le
  have hac : P ≪ Q := (klDiv_ne_top_iff.mp
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl)).1
  have hQpos : 0 < Q s := by
    by_contra h
    have hz : Q s = 0 := le_antisymm (not_lt.mp h) bot_le
    have hpz : P.real s = 0 := (measureReal_eq_zero_iff).mpr (hac hz)
    linarith
  have hq : 0 < Q.real s := ENNReal.toReal_pos (ne_of_gt hQpos) (measure_ne_top Q s)
  have hQc : 0 < Q sᶜ := by
    apply (ENNReal.toReal_pos_iff.mp _).1
    rw [show (Q sᶜ).toReal = Q.real sᶜ from rfl, probReal_compl_eq_one_sub hs]
    linarith
  have hevent := (event_binary_kl_le P Q s hs hQpos hQc).trans hkl
  have hreal : klB (P.real s) (Q.real s) ≤ (8/15 : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 8/15)).mp hevent
  have hsep := binary_kl_separation (5/8) (1/10) (P.real s) (Q.real s)
    (by norm_num) (by norm_num) (by norm_num) measureReal_nonneg measureReal_le_one hq hQ hp
  have hpin := Proofs.Tier2Information.binary_pinsker (5/8) (1/10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hpin
  linarith

theorem moderate_prefix_information {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (d : EntropyGap) (n : ℕ)
    (hn : (n : ℝ)*(d : ℝ)^2 ≤ 1/32) :
    klDiv (ν.prod (Tier2.finiteMeasure (signParameter d false) n))
      (ν.prod (Tier2.finiteMeasure (signParameter d true) n)) ≤
      ENNReal.ofReal (8/15 : ℝ) := by
  have hm := signParameter_interior d false
  have hp := signParameter_interior d true
  apply (seeded_prefix_kl_le_chisq ν _ _ hm.1 hm.2 hp.1 hp.2 n).trans
  apply ENNReal.ofReal_le_ofReal
  change (n : ℝ)*((1/2 + -(d : ℝ))-(1/2+(d : ℝ)))^2 /
    ((1/2+(d : ℝ))*(1-(1/2+(d : ℝ)))) ≤ 8/15
  have hden : 0 < (1/2+(d : ℝ))*(1-(1/2+(d : ℝ))) :=
    mul_pos (by linarith [d.property.1]) (by linarith [d.property.2])
  apply (div_le_iff₀ hden).mpr
  have hs := mul_nonneg (show 0 ≤ 1/8-(d : ℝ) by linarith [d.property.2])
    (show 0 ≤ 1/8+(d : ℝ) by linarith [d.property.1])
  nlinarith

/-- Every 1/10-correct observable test pays at least 1/(128 d²) under
the negative law. No termination or expected-work premise under the
positive or fair law is needed for this floor. -/
theorem single_gap_work {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : SignTest R) (d : EntropyGap)
    (hfinite : expectedSignTestWork ν (signParameter d false) A ≠ ∞)
    (hminus : (ν.prod (Tier2.tapeMeasure (signParameter d false))).real
      {z | A.output z = true} ≤ 1/10)
    (hplus : (ν.prod (Tier2.tapeMeasure (signParameter d true))).real
      {z | A.output z = false} ≤ 1/10) :
    (1/128 : ℝ) ≤ (d : ℝ)^2 *
      (expectedSignTestWork ν (signParameter d false) A).toReal := by
  let n := ⌊(1/32 : ℝ)/(d : ℝ)^2⌋₊
  have hd : 0 < (d : ℝ)^2 := sq_pos_of_pos d.property.1
  have hf := Nat.floor_le (show 0 ≤ (1/32 : ℝ)/(d : ℝ)^2 by positivity)
  have hn : (n : ℝ)*(d : ℝ)^2 ≤ 1/32 := (le_div_iff₀ hd).mp hf
  have hl := Nat.lt_floor_add_one ((1/32 : ℝ)/(d : ℝ)^2)
  have hl' : 1/32 < ((n : ℝ)+1)*(d : ℝ)^2 := (div_lt_iff₀ hd).mp hl
  have hs := mul_nonneg (show 0 ≤ 1/128-(d : ℝ) by linarith [d.property.2])
    (show 0 ≤ 1/128+(d : ℝ) by linarith [d.property.1])
  let P := ν.prod (Tier2.tapeMeasure (signParameter d false))
  have hearly : P.real {z | A.stop z ≤ n ∧ A.output z = false} ≤ 5/8 := by
    rw [← signTest_prefix_probability ν _ A n false]
    apply moderate_event_probability _ _ (A.prefixEvent n false)
      (A.measurable_prefixEvent n false) (moderate_prefix_information ν d n hn)
    rw [signTest_prefix_probability]
    exact (measureReal_mono (show {z | A.stop z ≤ n ∧ A.output z = false} ⊆
      {z | A.output z = false} from fun _ hz => hz.2)).trans hplus
  have hcover : Set.univ ⊆ {z | A.output z = true} ∪
      ({z | A.stop z ≤ n ∧ A.output z = false} ∪ {z | (n : ℕ∞) < A.stop z}) := by
    intro z _
    cases hb : A.output z
    · by_cases hstop : A.stop z ≤ n
      · exact Or.inr (Or.inl ⟨hstop, hb⟩)
      · exact Or.inr (Or.inr (lt_of_not_ge hstop))
    · exact Or.inl hb
  have hc := measureReal_mono (μ := P) hcover
  have hu := measureReal_union_le (μ := P) {z | A.output z = true}
    ({z | A.stop z ≤ n ∧ A.output z = false} ∪ {z | (n : ℕ∞) < A.stop z})
  have hv := measureReal_union_le (μ := P)
    {z | A.stop z ≤ n ∧ A.output z = false} {z | (n : ℕ∞) < A.stop z}
  rw [probReal_univ] at hc
  have htail : (11/40 : ℝ) ≤ P.real {z | (n : ℕ∞) < A.stop z} := by linarith
  have hw := signTest_late_probability ν (signParameter d false) A n hfinite
  have hm := mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hprod := mul_le_mul_of_nonneg_left (hm.trans hw) hd.le
  nlinarith

end ThresholdHC.CriticalAllSizes
