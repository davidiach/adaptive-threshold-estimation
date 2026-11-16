import ThresholdHC.ArbitraryLawController.LogSchedule

noncomputable section
set_option autoImplicit false
open Real Filter Asymptotics
namespace ThresholdHC.ArbitraryLawController
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.HardBudget ThresholdHC.Anytime

theorem repetitions_linear_bound {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4)
    {J : ℕ} (hJ : 1 ≤ J) (s : ℕ) :
    (repetitions δ s J : ℝ) ≤ (16 * log (4 * (J : ℝ) / δ) + 57) * ((s : ℝ) + 1) := by
  have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have harg : 0 < 4 * (J : ℝ) / δ := by positivity
  have hlog : 0 ≤ log (4 * (J : ℝ) / δ) :=
    log_nonneg ((le_div_iff₀ hd).mpr (by linarith))
  have h1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (s : ℝ) + 2 := by positivity
  have he : log (4 * (J : ℝ) / stageFailure δ s) =
      log (4 * (J : ℝ) / δ) + log ((s : ℝ) + 1) + log ((s : ℝ) + 2) := by
    have ha : 4 * (J : ℝ) / stageFailure δ s =
        (4 * (J : ℝ) / δ) * ((s : ℝ) + 1) * ((s : ℝ) + 2) := by
      unfold stageFailure
      field_simp
    rw [ha, log_mul (mul_pos harg h1).ne' h2.ne', log_mul harg.ne' h1.ne']
  have hl1 := log_le_sub_one_of_pos h1
  have hl2 := log_le_sub_one_of_pos h2
  have hl : log (4 * (J : ℝ) / stageFailure δ s) ≤ log (4 * (J : ℝ) / δ) + 2 * s + 3 := by
    rw [he]
    linarith
  have hl2lo : (1/2 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  have hp : pilotLog δ s J ≤ 2 * log (4 * (J : ℝ) / δ) + 4 * s + 6 := by
    apply (div_le_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    have hn : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    nlinarith
  have hc : (pilotGroups δ s J : ℝ) < pilotLog δ s J + 1 :=
    Nat.ceil_lt_add_one (pilotLog_nonneg hd hu s hJ)
  unfold repetitions
  push_cast
  nlinarith [mul_nonneg hlog (Nat.cast_nonneg s : (0 : ℝ) ≤ s)]

theorem depth_eventually {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4) (J : ℕ) :
    ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → J ≤ depth δ s := by
  by_cases hJ : J = 0
  · subst J
    exact ⟨0, fun _ _ => Nat.zero_le _⟩
  have hJ1 : 1 ≤ J := by omega
  let C := 2 * (16 * log (4 * (J : ℝ) / δ) + 57) * (4 : ℝ) ^ J
  have hl : 0 ≤ log (4 * (J : ℝ) / δ) := by
    apply log_nonneg
    apply (le_div_iff₀ hd).mpr
    have : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
    linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlin : (fun s : ℕ => (s : ℝ) + 1) =o[atTop] (fun s : ℕ => (2 : ℝ) ^ s) := by
    have h := (isLittleO_coe_const_pow_of_one_lt (R := ℝ) (by norm_num : (1 : ℝ) < 2)).add
      (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 0 (by norm_num : (1 : ℝ) < 2))
    simpa only [pow_zero] using h
  have he := (hlin.const_mul_left C).bound (by norm_num : (0 : ℝ) < 1)
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.mp he
  refine ⟨s₀, fun s hs => depth_maximal hJ1 ?_⟩
  have hb := hs₀ s hs
  simp only [Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _), one_mul] at hb
  have hb' := (le_abs_self (C * ((s : ℝ) + 1))).trans hb
  have hm := repetitions_linear_bound hd hu hJ1 s
  have hp := pilot_scale_upper (δ := δ) (s := s) hJ1
  have hp' : (pilotReservation δ s J : ℝ) ≤ (repetitions δ s J : ℝ) * (4 : ℝ) ^ J := by
    exact_mod_cast hp
  have ht : (2 * pilotReservation δ s J : ℕ) ≤ stageCap s := by
    have hr : 2 * (pilotReservation δ s J : ℝ) ≤ 4 * (2 : ℝ) ^ s := by
      have hx := mul_le_mul_of_nonneg_right hm (show (0 : ℝ) ≤ (4 : ℝ) ^ J by positivity)
      dsimp [C] at hb'
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s]
    exact_mod_cast hr
  exact ht

theorem completed_depth_eventually {δ : ℝ} (hd : 0 < δ) (hu : δ ≤ 1/4) (J : ℕ) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ B : ℕ, H ≤ B → ∃ s : ℕ,
      stageCount (B : ℝ) = s + 1 ∧ J ≤ depth δ s := by
  obtain ⟨s₀, hs₀⟩ := depth_eventually hd hu J
  refine ⟨paid (s₀ + 1), ?_, fun B hB => ?_⟩
  · exact (by omega : 1 ≤ s₀ + 1).trans (index_le_paid _)
  · have hf : paid (s₀ + 1) ≤ ⌊(B : ℝ)⌋₊ := by simpa using hB
    have hn := hf.trans_lt (next_exceeds (B : ℝ))
    have hi := paid_strict.lt_iff_lt.mp hn
    have hk : 0 < stageCount (B : ℝ) := by omega
    refine ⟨stageCount (B : ℝ) - 1, by omega, hs₀ _ (by omega)⟩

end ThresholdHC.ArbitraryLawController
