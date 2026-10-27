import ThresholdHC.CriticalEntropy.EventInformation

noncomputable section
open MeasureTheory InformationTheory Real
open scoped ENNReal

namespace ThresholdHC.CriticalEntropy

/-- Binary KL increases when two event probabilities move farther apart.
The first probability may equal one. -/
theorem binary_kl_separation (a b p q : ℝ) (hb : 0 < b) (hab : b < a)
    (ha1 : a < 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q)
    (hqb : q ≤ b) (hap : a ≤ p) : klB a b ≤ klB p q := by
  have ha : 0 < a := hb.trans hab
  have hb1 : 0 < 1-b := by linarith
  have ha0 : 0 < 1-a := by linarith
  have hq1 : 0 < 1-q := by linarith
  have hC : 1 ≤ a/b := (one_le_div hb).mpr hab.le
  have hD : (1-a)/(1-b) ≤ 1 := (div_le_one hb1).mpr (by linarith)
  have hCD : 0 ≤ a/b-(1-a)/(1-b) := by linarith
  have hlog : 0 ≤ log (a/b)-log ((1-a)/(1-b)) := by
    apply sub_nonneg.mpr
    exact log_le_log (div_pos ha0 hb1) (by linarith)
  have hfirst := Proofs.Tier2Information.kl_supporting_line p q a b hp0 hq.le
    (fun h => False.elim (hq.ne' h)) ha hb
  have hsecond := Proofs.Tier2Information.kl_supporting_line (1-p) (1-q) (1-a) (1-b)
    (by linarith) hq1.le (fun h => False.elim (hq1.ne' h)) ha0 hb1
  have hUp := mul_nonneg (sub_nonneg.mpr hap) hlog
  have hDown := mul_nonneg (sub_nonneg.mpr hqb) hCD
  have hcancelC : (a/b)*b=a := div_mul_cancel₀ a hb.ne'
  have hcancelD : ((1-a)/(1-b))*(1-b)=1-a := div_mul_cancel₀ (1-a) hb1.ne'
  unfold klB
  nlinarith

/-- The early-minus event cannot have probability above 9/40 when its
probability under the opposite sign is at most 1/10 and prefix KL is ≤1/48. -/
theorem early_event_probability {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (s : Set Ω) (hs : MeasurableSet s)
    (hkl : klDiv P Q ≤ ENNReal.ofReal (1/48 : ℝ))
    (hQ : Q.real s ≤ 1/10) : P.real s ≤ 9/40 := by
  by_contra hn
  have hp : (9/40 : ℝ) ≤ P.real s := (lt_of_not_ge hn).le
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
  have hreal : klB (P.real s) (Q.real s) ≤ (1/48 : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1/48)).mp hevent
  have hsep := binary_kl_separation (9/40) (1/10) (P.real s) (Q.real s)
    (by norm_num) (by norm_num) (by norm_num) measureReal_nonneg measureReal_le_one hq hQ hp
  have hpin := Proofs.Tier2Information.binary_pinsker (9/40) (1/10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hpin
  linarith

abbrev EntropyGap := {d : ℝ // 0 < d ∧ d ≤ 1/128}

def signParameter (d : EntropyGap) (b : Bool) : unitInterval :=
  ⟨1/2 + (if b then (d : ℝ) else -(d : ℝ)), by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith [d.property.1, d.property.2]⟩

theorem signParameter_interior (d : EntropyGap) (b : Bool) :
    0 < (signParameter d b : ℝ) ∧ (signParameter d b : ℝ) < 1 := by
  cases b <;> simp only [signParameter, Bool.false_eq_true, ↓reduceIte] <;>
    constructor <;> linarith [d.property.1, d.property.2]

/-- The information bound for the early prefix follows directly from the
chosen flip budget `n*d² ≤ 1/1024`. -/
theorem early_prefix_information {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (d : EntropyGap) (n : ℕ)
    (hn : (n : ℝ)*(d : ℝ)^2 ≤ 1/1024) :
    klDiv (ν.prod (Tier2.finiteMeasure (signParameter d false) n))
      (ν.prod (Tier2.finiteMeasure (signParameter d true) n)) ≤
      ENNReal.ofReal (1/48 : ℝ) := by
  have hm := signParameter_interior d false
  have hp := signParameter_interior d true
  apply (seeded_prefix_kl_le_chisq ν _ _ hm.1 hm.2 hp.1 hp.2 n).trans
  apply ENNReal.ofReal_le_ofReal
  change (n : ℝ)*((1/2 + -(d : ℝ))-(1/2+(d : ℝ)))^2 /
    ((1/2+(d : ℝ))*(1-(1/2+(d : ℝ)))) ≤ 1/48
  have hden : 0 < (1/2+(d : ℝ))*(1-(1/2+(d : ℝ))) :=
    mul_pos (by linarith [d.property.1]) (by linarith [d.property.2])
  apply (div_le_iff₀ hden).mpr
  have hs : (d : ℝ)^2 ≤ 1/16 := by
    have := mul_nonneg (show 0 ≤ 1/4-(d : ℝ) by linarith [d.property.2])
      (show 0 ≤ 1/4+(d : ℝ) by linarith [d.property.1])
    nlinarith
  nlinarith

end ThresholdHC.CriticalEntropy
