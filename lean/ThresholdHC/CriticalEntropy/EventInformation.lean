import ThresholdHC.CriticalEntropy.BernoulliPrefix
import ThresholdHC.Tier6.TestingFinite
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! Deterministic-prefix event transfer. Fair-coin stopping is not required. -/

noncomputable section
open MeasureTheory InformationTheory Real
open scoped ENNReal

namespace ThresholdHC.CriticalEntropy

theorem binary_kl_lower_log (p q : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hq : 0 < q) (hq1 : q < 1) : -p * log q - log 2 ≤ klB p q := by
  by_cases hpone : p = 1
  · simp only [hpone, klB, sub_self, zero_div, log_zero, zero_mul, add_zero,
      one_div, log_inv, neg_mul, one_mul]
    linarith [log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]
  have hpcomp : 0 < 1-p := sub_pos.mpr (lt_of_le_of_ne hp1 hpone)
  have hqcomp : 0 < 1-q := by linarith
  have hent := binEntropy_le_log_two (p := p)
  have hlog : log (1-q) ≤ 0 := log_nonpos hqcomp.le (by linarith)
  have hterm := mul_nonpos_of_nonneg_of_nonpos hpcomp.le hlog
  simp only [binEntropy, log_inv] at hent
  unfold klB
  rw [log_div hp.ne' hq.ne', log_div hpcomp.ne' hqcomp.ne']
  nlinarith

theorem event_binary_kl_le {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (s : Set Ω) (hs : MeasurableSet s) (hQ : 0 < Q s) (hQc : 0 < Q sᶜ) :
    ENNReal.ofReal (klB (P.real s) (Q.real s)) ≤ klDiv P Q := by
  classical
  let test : Ω → Bool := fun x => decide (x ∈ s)
  have ht : test ⁻¹' {true} = s := by ext x; simp [test]
  have hf : test ⁻¹' {false} = sᶜ := by ext x; simp [test]
  have hm : Measurable test := by
    apply measurable_to_bool
    rw [ht]
    exact hs
  have hpos (b : Bool) : 0 < (Q.map test) {b} := by
    rw [Measure.map_apply hm (measurableSet_singleton b)]
    cases b
    · simpa [hf] using hQc
    · simpa [ht] using hQ
  have hmap (M : Measure Ω) (b : Bool) :
      (M.map test).real {b} = if b then M.real s else M.real sᶜ := by
    rw [map_measureReal_apply hm (measurableSet_singleton b)]
    cases b <;> simp [ht, hf]
  have hid : klDiv (P.map test) (Q.map test) =
      ENNReal.ofReal (klB (P.real s) (Q.real s)) := by
    rw [Tier6.klDiv_finite_of_positive (P.map test) (Q.map test) hpos]
    simp only [Fintype.sum_bool, hmap, Bool.false_eq_true, ↓reduceIte]
    rw [probReal_compl_eq_one_sub hs, probReal_compl_eq_one_sub hs]
    rfl
  rw [← hid]
  exact klDiv_map_le P Q hm

/-- A measurable event with probability at least a quarter retains at least
exponentially small probability under a reference law of bounded KL. -/
theorem event_mass_lower_of_kl {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (s : Set Ω) (hs : MeasurableSet s) (D : ℝ) (hD : 0 ≤ D)
    (hkl : klDiv P Q ≤ ENNReal.ofReal D) (hP : (1/4 : ℝ) ≤ P.real s) :
    exp (-4*D-4*log 2) ≤ Q.real s := by
  have hac : P ≪ Q := (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl)).1
  have hQpos : 0 < Q s := by
    by_contra hn
    have hz : Q s = 0 := le_antisymm (not_lt.mp hn) bot_le
    have hpz : P.real s = 0 := (measureReal_eq_zero_iff).mpr (hac hz)
    linarith
  have hq : 0 < Q.real s := ENNReal.toReal_pos (ne_of_gt hQpos) (measure_ne_top Q s)
  by_cases hqone : Q.real s = 1
  · rw [hqone]
    exact exp_le_one_iff.mpr (by linarith [log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)])
  have hq1 : Q.real s < 1 := lt_of_le_of_ne measureReal_le_one hqone
  have hQc : 0 < Q sᶜ := by
    apply (ENNReal.toReal_pos_iff.mp _).1
    rw [show (Q sᶜ).toReal = Q.real sᶜ from rfl, probReal_compl_eq_one_sub hs]
    linarith
  have hb := (event_binary_kl_le P Q s hs hQpos hQc).trans hkl
  have hbreal : klB (P.real s) (Q.real s) ≤ D :=
    (ENNReal.ofReal_le_ofReal_iff hD).mp hb
  have hl := binary_kl_lower_log (P.real s) (Q.real s) (by linarith)
    measureReal_le_one hq hq1
  have hlog : log (Q.real s) ≤ 0 := log_nonpos hq.le hq1.le
  have hmul := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hP) hlog
  have hbound : -4*D-4*log 2 ≤ log (Q.real s) := by nlinarith
  exact (exp_le_exp.mpr hbound).trans_eq (exp_log hq)

/-- Event transfer for the constructed seed/Bernoulli experiment, with the
KL cost derived from the flip parameters rather than supplied as an assumption. -/
theorem prefix_event_mass_lower {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (p q : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hq : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) (n : ℕ)
    (s : Set (R × (Fin n → Bool))) (hs : MeasurableSet s)
    (hP : (1/4 : ℝ) ≤ (ν.prod (Tier2.finiteMeasure p n)).real s) :
    exp (-4*(n*((p : ℝ)-q)^2/((q : ℝ)*(1-q)))-4*log 2) ≤
      (ν.prod (Tier2.finiteMeasure q n)).real s := by
  apply event_mass_lower_of_kl _ _ s hs _
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      (mul_nonneg hq.le (by linarith)))
    (seeded_prefix_kl_le_chisq ν p q hp hp1 hq hq1 n) hP

/-- The exponential constant in BC3, for a finite event under the fair coin.
The sole cost hypothesis bounds the deterministic prefix length. -/
theorem fair_prefix_event_mass_lower {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (n : ℕ) (c : ℝ) (hcost : n*((p : ℝ)-1/2)^2 ≤ 4*c+1/4)
    (s : Set (R × (Fin n → Bool))) (hs : MeasurableSet s)
    (hP : (1/4 : ℝ) ≤ (ν.prod (Tier2.finiteMeasure p n)).real s) :
    exp (-64*c-8) ≤ (ν.prod (Tier2.finiteMeasure ⟨1/2, by norm_num⟩ n)).real s := by
  have h := prefix_event_mass_lower ν p ⟨1/2, by norm_num⟩ hp hp1
    (by norm_num) (by norm_num) n s hs hP
  apply le_trans _ h
  apply exp_le_exp.mpr
  norm_num
  have hlog : log (2 : ℝ) ≤ 1 := by
    have := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  nlinarith

end ThresholdHC.CriticalEntropy
