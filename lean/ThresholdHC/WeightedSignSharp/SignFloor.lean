import ThresholdHC.WeightedSignSharp.CappedSign

/-! The stopped change-of-measure floor `d² E₋τ > 3/40`.

The test is capped at `N = ⌈10 E₋τ⌉ + 1`. Markov's inequality leaves the
capped minus decision with minus-law mass at least `4/5`, and its plus-law
mass is at most `1/10`. Binary data processing, the exact stopped chain rule
for the capped transcript and the chi-square bound on one flip then give
`kl(4/5, 1/10) ≤ E₋τ · 4d²/(1/4 - d²)`. No fair-law or plus-law work is
assumed. -/

noncomputable section
open MeasureTheory InformationTheory Real
open scoped ENNReal
namespace ThresholdHC.WeightedSignSharp
open ThresholdHC.CriticalEntropy

theorem binary_kl_four_fifths : (9/5) * log 2 ≤ klB (4/5) (1/10) := by
  unfold klB
  have h8 : log ((4/5 : ℝ) / (1/10)) = 3 * log 2 := by
    rw [show (4/5 : ℝ) / (1/10) = 2^3 by norm_num, Real.log_pow]
    norm_num
  have h29 : log ((1 - 4/5 : ℝ) / (1 - 1/10)) = log 2 - log 9 := by
    rw [show (1 - 4/5 : ℝ) / (1 - 1/10) = 2/9 by norm_num,
      Real.log_div (by norm_num) (by norm_num)]
  have h9 : log (9 : ℝ) ≤ 4 * log 2 := by
    rw [show (4 : ℝ) * log 2 = log (2^4) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by norm_num) (by norm_num)
  rw [h8, h29]
  linarith

theorem sign_work_floor_proof : SignWorkFloorStatement := by
  intro R _ ν _ A d hfinite hminus hplus
  set w := (expectedSignTestWork ν (signParameter d false) A).toReal with hw_def
  have hw0 : 0 ≤ w := ENNReal.toReal_nonneg
  set N : ℕ := ⌈10 * w⌉₊ + 1 with hN_def
  have hN : 10 * w < N := by
    have h := Nat.le_ceil (10 * w)
    rw [hN_def, Nat.cast_add, Nat.cast_one]
    linarith
  set Pm := ν.prod (Tier2.tapeMeasure (signParameter d false)) with hPm
  set Pp := ν.prod (Tier2.tapeMeasure (signParameter d true)) with hPp
  set F : Set (R × (ℕ → Bool)) := {z | A.stop z ≤ N ∧ A.output z = false} with hF
  have hlate : Pm.real {z | (N : ℕ∞) < A.stop z} ≤ 1/10 := by
    have h := signTest_late_probability ν (signParameter d false) A N hfinite
    have hP0 : 0 ≤ Pm.real {z | (N : ℕ∞) < A.stop z} := measureReal_nonneg
    by_contra hc
    rw [not_le] at hc
    have hm := mul_lt_mul_of_pos_left hc (lt_of_le_of_lt (by positivity) hN :
      (0 : ℝ) < N)
    nlinarith
  have hFm : (4/5 : ℝ) ≤ Pm.real F := by
    have hcover : Set.univ ⊆ {z | A.output z = true} ∪
        (F ∪ {z | (N : ℕ∞) < A.stop z}) := by
      intro z _
      cases hb : A.output z
      · by_cases hstop : A.stop z ≤ N
        · exact Or.inr (Or.inl ⟨hstop, hb⟩)
        · exact Or.inr (Or.inr (lt_of_not_ge hstop))
      · exact Or.inl hb
    have hc := measureReal_mono (μ := Pm) hcover
    have hu := measureReal_union_le (μ := Pm) {z | A.output z = true}
      (F ∪ {z | (N : ℕ∞) < A.stop z})
    have hv := measureReal_union_le (μ := Pm) F {z | (N : ℕ∞) < A.stop z}
    rw [probReal_univ] at hc
    linarith
  have hFp : Pp.real F ≤ 1/10 :=
    (measureReal_mono (show F ⊆ {z | A.output z = false} from fun _ hz => hz.2)).trans hplus
  set B := cappedSignProcedure A N with hB
  have hcap : ∀ z, B.stop z ≤ N := cappedSignProcedure_cap A N
  have hT : Measurable (cappedTranscript B N) := measurable_cappedTranscript B N
  set Qm := Pm.map (cappedTranscript B N) with hQm
  set Qp := Pp.map (cappedTranscript B N) with hQp
  set S := cappedFalseEvent A N with hS_def
  have hS : MeasurableSet S := measurable_cappedFalseEvent A N
  have hQmS : Qm.real S = Pm.real F := by
    rw [hQm, map_measureReal_apply hT hS, hS_def, hB, cappedTranscript_preimage_false]
  have hQpS : Qp.real S = Pp.real F := by
    rw [hQp, map_measureReal_apply hT hS, hS_def, hB, cappedTranscript_preimage_false]
  have hm := signParameter_interior d false
  have hp := signParameter_interior d true
  set wB := (expectedStoppedProcedureWork ν (signParameter d false) B).toReal with hwB
  set kq := klB (signParameter d false) (signParameter d true) with hkq
  have hkl : klDiv Qm Qp = ENNReal.ofReal (wB * kq) :=
    PsiNull.capped_transcript_kl ν B N hcap (signParameter d false) (signParameter d true)
      hm.1 hm.2 hp.1 hp.2
  have hQpos : 0 < Qp S := by
    by_contra h
    have hz : Qp S = 0 := le_antisymm (not_lt.mp h) bot_le
    have hac : Qm ≪ Qp := (klDiv_ne_top_iff.mp (by rw [hkl]; exact ENNReal.ofReal_ne_top)).1
    have h0 : Qm.real S = 0 := (measureReal_eq_zero_iff).mpr (hac hz)
    linarith
  have hQc : 0 < Qp Sᶜ := by
    apply (ENNReal.toReal_pos_iff.mp _).1
    rw [show (Qp Sᶜ).toReal = Qp.real Sᶜ from rfl, probReal_compl_eq_one_sub hS]
    linarith
  have hq : 0 < Qp.real S := ENNReal.toReal_pos (ne_of_gt hQpos) (measure_ne_top Qp S)
  have hsep := binary_kl_separation (4/5) (1/10) (Qm.real S) (Qp.real S)
    (by norm_num) (by norm_num) (by norm_num) measureReal_nonneg measureReal_le_one hq
    (by rw [hQpS]; exact hFp) (by rw [hQmS]; exact hFm)
  have hK := binary_kl_four_fifths
  have hlog2 := Real.log_two_gt_d9
  have hev := (event_binary_kl_le Qm Qp S hS hQpos hQc).trans_eq hkl
  rw [ENNReal.ofReal_le_ofReal_iff'] at hev
  have hev' : klB (Qm.real S) (Qp.real S) ≤ wB * kq := hev.resolve_right (by
    intro h
    linarith)
  have hchi := binary_kl_le_chisq _ _ hm.1 hm.2 hp.1 hp.2
  have hwB0 : 0 ≤ wB := ENNReal.toReal_nonneg
  have hwBw : wB ≤ w := ENNReal.toReal_mono hfinite (cappedSign_work_le ν _ A N)
  have hden : 0 < (1/2 + (d : ℝ)) * (1 - (1/2 + (d : ℝ))) :=
    mul_pos (by linarith [d.property.1]) (by linarith [d.property.2])
  have hchi' : kq ≤ 4 * (d : ℝ)^2 / ((1/2 + (d : ℝ)) * (1 - (1/2 + (d : ℝ)))) := by
    have he : ((signParameter d false : ℝ) - (signParameter d true : ℝ))^2 /
        ((signParameter d true : ℝ) * (1 - (signParameter d true : ℝ))) =
        4 * (d : ℝ)^2 / ((1/2 + (d : ℝ)) * (1 - (1/2 + (d : ℝ)))) := by
      change ((1/2 + -(d : ℝ)) - (1/2 + (d : ℝ)))^2 /
        ((1/2 + (d : ℝ)) * (1 - (1/2 + (d : ℝ)))) = _
      congr 1
      ring
    rw [hkq]
    exact hchi.trans_eq he
  have hchain : klB (4/5) (1/10) ≤
      w * (4 * (d : ℝ)^2 / ((1/2 + (d : ℝ)) * (1 - (1/2 + (d : ℝ))))) := by
    calc klB (4/5) (1/10) ≤ klB (Qm.real S) (Qp.real S) := hsep
      _ ≤ wB * kq := hev'
      _ ≤ wB * (4 * (d : ℝ)^2 / ((1/2 + (d : ℝ)) * (1 - (1/2 + (d : ℝ))))) :=
        mul_le_mul_of_nonneg_left hchi' hwB0
      _ ≤ w * (4 * (d : ℝ)^2 / ((1/2 + (d : ℝ)) * (1 - (1/2 + (d : ℝ))))) :=
        mul_le_mul_of_nonneg_right hwBw (by positivity)
  rw [mul_div_assoc', le_div_iff₀ hden] at hchain
  have hdsq : (d : ℝ)^2 ≤ 1/16384 := by
    have h := (sq_le_sq₀ d.property.1.le (by norm_num : (0 : ℝ) ≤ 1/128)).mpr d.property.2
    norm_num at h ⊢
    exact h
  have hD : (4095/16384 : ℝ) ≤ (1/2 + (d : ℝ)) * (1 - (1/2 + (d : ℝ))) := by nlinarith
  have hKl : (1247/1000 : ℝ) ≤ klB (4/5) (1/10) := by linarith
  have hprod := mul_le_mul hKl hD (by norm_num) (by linarith)
  nlinarith

end ThresholdHC.WeightedSignSharp
