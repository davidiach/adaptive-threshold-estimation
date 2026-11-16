import ThresholdHC.ArbitraryLawController.Budget

noncomputable section
set_option autoImplicit false
open Real
namespace ThresholdHC.ArbitraryLawController
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.HardBudget ThresholdHC.Anytime

theorem median_schedule_failure {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    (s : ℕ) {J : ℕ} (hJ : 1 ≤ J) :
    (3/4 : ℝ) ^ (4 * pilotGroups δ s J) / 2 ≤ stageFailure δ s / 2 := by
  have hf := stageFailure_pos hd s
  have hc : pilotLog δ s J ≤ (pilotGroups δ s J : ℝ) := Nat.le_ceil _
  have hc' := (div_le_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))).mp hc
  have hl2 : log (2 : ℝ) ≤ 1 := by linarith [log_two_lt_d9]
  have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hl := log_le_log (one_div_pos.mpr hf)
    (div_le_div_of_nonneg_right (show (1 : ℝ) ≤ 4 * J by linarith) hf.le)
  have hg : log (1 / stageFailure δ s) ≤ (pilotGroups δ s J : ℝ) := by
    have hn : (0 : ℝ) ≤ (pilotGroups δ s J : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hp : log (3/4 : ℝ) ≤ -(1/4) := by
    linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3/4)]
  have he := exp_le_exp.mpr (show ((4 * pilotGroups δ s J : ℕ) : ℝ) * log (3/4 : ℝ) ≤
      -log (1 / stageFailure δ s) by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (pilotGroups δ s J))])
  rw [exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 3/4), exp_neg,
    exp_log (one_div_pos.mpr hf)] at he
  have he' : (3/4 : ℝ) ^ (4 * pilotGroups δ s J) ≤ stageFailure δ s := by simpa using he
  linarith

theorem repetitions_log_bound {δ B : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    (hB : 0 ≤ B) {s : ℕ} (hs : stageCount B = s + 1)
    (hJ : 1 ≤ depth δ s) :
    (repetitions δ s (depth δ s) : ℝ) ≤ 64 * inflation B δ := by
  let L := inflation B δ
  let J := depth δ s
  have hL1 : 1 ≤ L := (ThresholdHC.Confidence.confidence_log_ge_one hd hu).trans (inflation_ge_log hB)
  have hL0 : 0 ≤ L := by linarith
  have hcount := count_log_bound hB
  rw [hs] at hcount
  push_cast at hcount
  have hdepth : (J : ℝ) ≤ (s : ℝ) + 2 := by exact_mod_cast depth_le δ s
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have harg : 0 ≤ log (2 + logBudget B) := log_nonneg (by
    have := logBudget_nonneg hB
    linarith)
  have hℓ0 : 0 ≤ log (1/δ) := (ThresholdHC.Confidence.confidence_log_pos hd hu).le
  have hlogJ : log (J : ℝ) ≤ L := by
    have h := log_le_log hJ0 (show (J : ℝ) ≤ 2 + logBudget B by linarith)
    dsimp [L, inflation]
    linarith
  have hlog4 : log (4 : ℝ) ≤ L := by
    apply (log_le_log (by norm_num : (0 : ℝ) < 4) ?_).trans (inflation_ge_log hB)
    exact (le_div_iff₀ hd).mpr (by linarith)
  have hf := stageFailure_pos hd s
  have hlogA : log (4 * (J : ℝ) / stageFailure δ s) ≤ 3 * L := by
    have he : log (4 * (J : ℝ) / stageFailure δ s) =
        log 4 + log (J : ℝ) + log (1 / stageFailure δ s) := by
      rw [log_div (mul_pos (by norm_num) hJ0).ne' hf.ne',
        log_mul (by norm_num : (4 : ℝ) ≠ 0) hJ0.ne', log_div one_ne_zero hf.ne', log_one]
      ring
    rw [he]
    have := stage_log_le hB hd hs
    linarith
  have hl2 : (1/2 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  have hpl : pilotLog δ s J ≤ 6 * L := by
    apply (div_le_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    nlinarith
  have hc : (pilotGroups δ s J : ℝ) < pilotLog δ s J + 1 :=
    Nat.ceil_lt_add_one (pilotLog_nonneg hd hu s hJ)
  change ((8 * pilotGroups δ s J + 1 : ℕ) : ℝ) ≤ _
  push_cast
  linarith

theorem effective_budget {δ B : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    (hB : 0 ≤ B) {s : ℕ} (hs : stageCount B = s + 1)
    (hJ : 1 ≤ depth δ s) :
    B / (4096 * inflation B δ) < (4 : ℝ) ^ depth δ s := by
  have hL := inflation_pos hB hd hu
  have hm := repetitions_log_bound hd hu hB hs hJ
  have hc := (completed_stage_bounds hB hs).2
  have hn : (stageCap s : ℝ) < 16 * (repetitions δ s (depth δ s) : ℝ) *
      (4 : ℝ) ^ depth δ s := by exact_mod_cast (selected_scale hd hu s hJ).1
  apply (div_lt_iff₀ (by positivity : 0 < 4096 * inflation B δ)).mpr
  have hp : (0 : ℝ) ≤ (4 : ℝ) ^ depth δ s := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hm hp]

end ThresholdHC.ArbitraryLawController
