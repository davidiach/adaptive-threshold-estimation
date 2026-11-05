import ThresholdHC.Tier6.TestingFinite
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

noncomputable section
open MeasureTheory InformationTheory Real
open scoped ENNReal
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier6

theorem binary_event_log_bound {p q : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    (hq : 0 < q ∧ q < 1) :
    -p*log q-log 2 ≤ klB p q := by
  have he : klB p q = -binEntropy p-p*log q-(1-p)*log (1-q) := by
    by_cases hp0 : p = 0
    · simp [hp0,klB]
    by_cases hp1 : p = 1
    · simp [hp1,klB]
    rw [klB,log_div hp0 hq.1.ne',log_div (sub_ne_zero.mpr (Ne.symm hp1))
      (ne_of_gt (sub_pos.mpr hq.2)),binEntropy,log_inv,log_inv]
    ring
  have hh := binEntropy_le_log_two (p := p)
  have hlog : log (1-q) ≤ 0 := log_nonpos (by linarith) (by linarith)
  rw [he]
  nlinarith only [hh,mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hp.2) hlog]

/-- A high-power event cannot be too rare under a law with bounded KL.
This one-sided testing bound will be applied to disjoint first-crossing events. -/
theorem event_probability_lower {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (s : Set Ω) (hs : MeasurableSet s) {δ K : ℝ}
    (hd : 0 ≤ δ ∧ δ ≤ 1/2) (hK : 0 ≤ K)
    (hP : 1-δ ≤ P.real s) (hkl : klDiv P Q ≤ ENNReal.ofReal K) :
    exp (-K/(1-δ))/4 ≤ Q.real s := by
  classical
  have hδ : 0 < 1-δ := by linarith
  have hac := (klDiv_ne_top_iff.mp (ne_of_lt (hkl.trans_lt ENNReal.ofReal_lt_top))).1
  have hQpos : 0 < Q.real s := by
    by_contra hn
    have hq : Q.real s = 0 := le_antisymm (not_lt.mp hn) measureReal_nonneg
    have hp : P.real s = 0 := (measureReal_eq_zero_iff).mpr (hac ((measureReal_eq_zero_iff).mp hq))
    linarith
  have hQone : Q.real s ≤ 1 := measureReal_le_one
  by_cases hQeq : Q.real s = 1
  · rw [hQeq]
    have he : exp (-K/(1-δ)) ≤ 1 := exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
    linarith
  have hQlt : Q.real s < 1 := lt_of_le_of_ne hQone hQeq
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
    · rw [hfalse]
      apply ENNReal.toReal_pos_iff.mp ?_ |>.1
      change 0 < Q.real sᶜ
      rw [probReal_compl_eq_one_sub hs]
      linarith
    · rw [htrue]
      exact (ENNReal.toReal_pos_iff.mp hQpos).1
  have hmap (M : Measure Ω) (b : Bool) :
      (M.map test).real {b} = if b then M.real s else M.real sᶜ := by
    rw [map_measureReal_apply htest (measurableSet_singleton b)]
    cases b <;> simp [htrue,hfalse]
  have hid : klDiv (P.map test) (Q.map test) = ENNReal.ofReal (klB (P.real s) (Q.real s)) := by
    rw [klDiv_finite_of_positive (P.map test) (Q.map test) hmapQ]
    simp only [Fintype.sum_bool,hmap,Bool.false_eq_true,↓reduceIte]
    rw [probReal_compl_eq_one_sub hs,probReal_compl_eq_one_sub hs]
    rfl
  have hk : klB (P.real s) (Q.real s) ≤ K := by
    apply (ENNReal.ofReal_le_ofReal_iff hK).mp
    rw [← hid]
    exact (klDiv_map_le P Q htest).trans hkl
  have hb := binary_event_log_bound (p := P.real s) ⟨measureReal_nonneg,measureReal_le_one⟩ ⟨hQpos,hQlt⟩
  have hlq : log (Q.real s) ≤ 0 := log_nonpos hQpos.le hQone
  have hm := mul_le_mul_of_nonneg_right hP (neg_nonneg.mpr hlq)
  have hl : -(K+log 2)/(1-δ) ≤ log (Q.real s) := by
    apply (div_le_iff₀ hδ).mpr
    nlinarith only [hm,hb,hk]
  have hlog2 : 0 ≤ log 2 := log_nonneg (by norm_num)
  have hscalar : -K/(1-δ)-2*log 2 ≤ -(K+log 2)/(1-δ) := by
    apply (le_div_iff₀ hδ).mpr
    have hc : (-K/(1-δ))*(1-δ) = -K := div_mul_cancel₀ _ hδ.ne'
    nlinarith only [hc,mul_nonneg hlog2 (show 0 ≤ 1-2*δ by linarith)]
  have he := exp_le_exp.mpr (hscalar.trans hl)
  rw [exp_log hQpos,exp_sub,show exp (2*log 2) = (4:ℝ) by
    rw [show (2:ℝ)*log 2 = log 2+log 2 by ring,exp_add,exp_log (by norm_num)]
    norm_num] at he
  exact he

end ThresholdHC.AnytimeLower
