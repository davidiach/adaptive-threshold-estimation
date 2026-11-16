import ThresholdHC.ArbitraryLawController.Schedule
import ThresholdHC.RobustContinuation.PaidMedian

/-! The exact pilot repetitions, continuation reservation, and (A17)--(A18). -/

noncomputable section
set_option autoImplicit false
open Real
namespace ThresholdHC.ArbitraryLawController
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.HardBudget ThresholdHC.Anytime
open ThresholdHC.RobustContinuation

theorem pilotLog_nonneg {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    (s : ℕ) {J : ℕ} (hJ : 1 ≤ J) : 0 ≤ pilotLog δ s J := by
  have hf := stageFailure_pos hd s
  have hfu := (stageFailure_le hd.le s).trans hu
  have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  apply div_nonneg _ (log_pos (by norm_num)).le
  apply log_nonneg
  exact (le_div_iff₀ hf).mpr (by linarith)

theorem repetitions_pilot_error {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    (s : ℕ) {J : ℕ} (_hJ : 1 ≤ J) :
    8 * log (2 * (J : ℝ) / (stageFailure δ s / 2)) ≤ repetitions δ s J := by
  have hc : pilotLog δ s J ≤ (pilotGroups δ s J : ℝ) := Nat.le_ceil _
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlog2u : log (2 : ℝ) ≤ 1 := by linarith [log_two_lt_d9]
  have hc' := (div_le_iff₀ hlog2).mp hc
  have hg : 0 ≤ (pilotGroups δ s J : ℝ) := Nat.cast_nonneg _
  have he : 2 * (J : ℝ) / (stageFailure δ s / 2) = 4 * J / stageFailure δ s := by ring
  rw [he]
  unfold repetitions
  push_cast
  nlinarith

theorem pilotLog_next {δ : ℝ} (hd : 0 < δ) (s : ℕ) {J : ℕ} (hJ : 1 ≤ J) :
    pilotLog δ s (J + 1) ≤ pilotLog δ s J + 1 := by
  have hf := stageFailure_pos hd s
  have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have ha : 0 < 4 * (J : ℝ) / stageFailure δ s := by positivity
  have hb : 0 < 4 * ((J + 1 : ℕ) : ℝ) / stageFailure δ s := by positivity
  have harg : 4 * ((J + 1 : ℕ) : ℝ) / stageFailure δ s ≤
      2 * (4 * (J : ℝ) / stageFailure δ s) := by
    push_cast
    rw [← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right hf).mpr
    linarith
  have hl := log_le_log hb harg
  rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) ha.ne'] at hl
  unfold pilotLog
  apply (div_le_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  field_simp at ⊢
  linarith

theorem repetitions_next {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    (s : ℕ) {J : ℕ} (hJ : 1 ≤ J) :
    repetitions δ s (J + 1) ≤ 2 * repetitions δ s J := by
  have hg : pilotGroups δ s (J + 1) ≤ pilotGroups δ s J + 1 := by
    apply Nat.ceil_le.mpr
    have hc : pilotLog δ s J ≤ (pilotGroups δ s J : ℝ) := Nat.le_ceil _
    exact (pilotLog_next hd s hJ).trans (by push_cast; linarith)
  have hp : 0 < pilotGroups δ s J := by
    apply Nat.ceil_pos.mpr
    apply div_pos _ (log_pos (by norm_num))
    apply log_pos
    have hf := stageFailure_pos hd s
    have hfu := (stageFailure_le hd.le s).trans hu
    have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    exact (lt_div_iff₀ hf).mpr (by linarith)
  unfold repetitions
  omega

theorem selected_scale {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    (s : ℕ) (hJ : 1 ≤ depth δ s) :
    stageCap s < 16 * repetitions δ s (depth δ s) * 4 ^ depth δ s ∧
      repetitions δ s (depth δ s) * 4 ^ depth δ s ≤ stageCap s := by
  have hn := next_depth_exceeds δ s
  have huP := pilot_scale_upper (δ := δ) (s := s) (by omega : 1 ≤ depth δ s + 1)
  have hm := repetitions_next hd hu s hJ
  have hpow : 4 ^ (depth δ s + 1) = 4 ^ depth δ s * 4 := pow_succ _ _
  rw [hpow] at huP
  have hp := Nat.mul_le_mul_right (4 ^ depth δ s * 4) hm
  refine ⟨by nlinarith, (pilot_scale_lower hJ).trans (depth_fits δ s)⟩

theorem continuation_base_ge {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    (s : ℕ) (hJ : 1 ≤ depth δ s) :
    (4 : ℝ) ^ depth δ s / 16 ≤
      medianBaseBudget (remaining δ s) (4 * pilotGroups δ s (depth δ s)) := by
  have hs := (selected_scale hd hu s hJ).2
  have hr := (remaining_bounds δ s).2.1
  have hc : 0 < (repetitions δ s (depth δ s) : ℝ) := by exact_mod_cast repetitions_pos δ s _
  have hm : (2 * ((4 * pilotGroups δ s (depth δ s) : ℕ) : ℝ) + 1) =
      (repetitions δ s (depth δ s) : ℝ) := by simp [repetitions]; ring
  unfold medianBaseBudget
  rw [hm]
  apply (le_div_iff₀ (by positivity : 0 < 8 * (repetitions δ s (depth δ s) : ℝ))).mpr
  have hs' : (repetitions δ s (depth δ s) : ℝ) * (4 : ℝ) ^ depth δ s ≤ stageCap s := by exact_mod_cast hs
  have hr' : (stageCap s : ℝ) ≤ 2 * (remaining δ s : ℝ) := by exact_mod_cast hr
  nlinarith

end ThresholdHC.ArbitraryLawController
