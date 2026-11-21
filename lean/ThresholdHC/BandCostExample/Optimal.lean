import ThresholdHC.BandCostExample.Rearrange
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The two largest gaps are the strict unique minimum of the inner cost over
all `2^64` hard masks, the cap is inactive, and the original functional over all
submeasures takes the hard minimum. With `u = √c ∈ (1.732, 1.735)`,
`a = √((1 + log 2)/2) < 0.9202` and `X` the retained gap sum, the comparison
reduces to `a - 3u/4 < √((k + k log k)/4) - u X`, checked by cases on the number
`k` of retained atoms. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.BandCostExample
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

theorem ent_zero : ent 0 = 0 := by simp [ent]

theorem ent_one : ent 1 = 1 := by simp [ent]

theorem ent_two : ent 2 = 2 + 2 * Real.log 2 := by simp [ent]

theorem ent_three : ent 3 = 3 + 3 * Real.log 3 := by simp [ent]

theorem one_le_log_three : 1 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

theorem a_lt : Real.sqrt (ent 2 / 4) < 0.9202 := by
  rw [Real.sqrt_lt' (by norm_num), ent_two]
  have := Real.log_two_lt_d9
  norm_num
  linarith

theorem u_gt : 1.732 < Real.sqrt cc := by
  rw [Real.lt_sqrt (by norm_num)]
  have := three_lt_cc
  norm_num
  linarith

theorem u_lt : Real.sqrt cc < 1.735 := by
  rw [Real.sqrt_lt' (by norm_num)]
  have := cc_le
  norm_num
  linarith

theorem sqrt_ent_one : Real.sqrt (ent 1 / 4) = 1/2 := by
  rw [ent_one, show (1:ℝ)/4 = (1/2)^2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem sqrt_ent_three : 1.2247 < Real.sqrt (ent 3 / 4) := by
  rw [Real.lt_sqrt (by norm_num), ent_three]
  have := one_le_log_three
  norm_num
  linarith

theorem sqrt_ent_big (k : ℕ) : 1.4142 < Real.sqrt (ent (k+4) / 4) := by
  rw [Real.lt_sqrt (by norm_num)]
  have hk : (4:ℝ) ≤ ((k+4 : ℕ) : ℝ) := by
    have : (4:ℕ) ≤ k+4 := by omega
    exact_mod_cast this
  have hl : 1 ≤ Real.log ((k+4 : ℕ) : ℝ) :=
    one_le_log_three.trans (Real.log_le_log (by norm_num) (by linarith))
  have hp : ((k+4 : ℕ) : ℝ) ≤ ((k+4 : ℕ) : ℝ) * Real.log ((k+4 : ℕ) : ℝ) := by
    nlinarith
  have he : ent (k+4) = ((k+4 : ℕ) : ℝ) + ((k+4 : ℕ) : ℝ) * Real.log ((k+4 : ℕ) : ℝ) := rfl
  have hn : (1.4142 : ℝ)^2 < 2 := by norm_num
  rw [he]
  linarith

/-- The reduced comparison, by cases on the number `k` of retained atoms. -/
theorem core (k : ℕ) (x : ℝ) (hX : x ≤ 1 - (1/2 : ℝ)^k) (h2 : k = 2 → x ≤ 5/8) :
    Real.sqrt (ent 2 / 4) - 3/4 * Real.sqrt cc < Real.sqrt (ent k / 4) - Real.sqrt cc * x := by
  have ha := a_lt
  have hu1 := u_gt
  have hu2 := u_lt
  have hu0 : 0 ≤ Real.sqrt cc := Real.sqrt_nonneg _
  obtain _ | _ | _ | _ | k := k
  · have hx : x ≤ 0 := by simpa using hX
    have hux := mul_le_mul_of_nonneg_left hx hu0
    rw [ent_zero, zero_div, Real.sqrt_zero]
    linarith
  · have hx : x ≤ 1/2 := by norm_num at hX; linarith
    have hux := mul_le_mul_of_nonneg_left hx hu0
    rw [sqrt_ent_one]
    linarith
  · have hx : x ≤ 5/8 := h2 rfl
    have hux := mul_le_mul_of_nonneg_left hx hu0
    linarith
  · have hx : x ≤ 7/8 := by norm_num at hX; linarith
    have hux := mul_le_mul_of_nonneg_left hx hu0
    have hs := sqrt_ent_three
    linarith
  · have hp : (0:ℝ) ≤ (1/2)^(k+4) := by positivity
    have hx : x ≤ 1 := by linarith
    have hux := mul_le_mul_of_nonneg_left hx hu0
    have hs := sqrt_ent_big k
    linarith

theorem V_topTwo : V topTwo =
    hh * (Real.sqrt cc * Real.sqrt (ent 2 / 4)) + TT - cc * hh * (3/4) := by
  rw [V, kc_topTwo, saved_topTwo]

/-- Every other hard mask has larger uncapped inner cost. -/
theorem V_lt (s : Fin 64 → Bool) (hs : s ≠ topTwo) : V topTwo < V s := by
  have hc := core (kc s) (X s) (X_le s) (fun hk => X_pair s hk hs)
  have hpos : 0 < hh * Real.sqrt cc := mul_pos hh_pos (Real.sqrt_pos.mpr cc_pos)
  have hm := mul_lt_mul_of_pos_left hc hpos
  have hcc : cc = Real.sqrt cc * Real.sqrt cc := (Real.mul_self_sqrt cc_pos.le).symm
  have e1 : hh * Real.sqrt cc * (Real.sqrt (ent 2 / 4) - 3/4 * Real.sqrt cc) =
      hh * (Real.sqrt cc * Real.sqrt (ent 2 / 4)) - cc * hh * (3/4) := by
    linear_combination (3/4 * hh) * hcc
  have e2 : hh * Real.sqrt cc * (Real.sqrt (ent (kc s) / 4) - Real.sqrt cc * X s) =
      hh * (Real.sqrt cc * Real.sqrt (ent (kc s) / 4)) - cc * hh * X s := by
    linear_combination (hh * X s) * hcc
  have hsv := saved_le s
  rw [V_topTwo, V]
  linarith

/-- The hard minimum is far below the cap `1/4`. -/
theorem V_topTwo_lt_cap : V topTwo < 1/4 := by
  have hT : TT ≤ cc * hh := by
    have h := TT_le_sum
    have h2 := mul_le_mul_of_nonneg_left atoms_sum_le
      (mul_nonneg cc_pos.le hh_pos.le)
    linarith
  have hua : Real.sqrt cc * Real.sqrt (ent 2 / 4) ≤ 1.735 * 0.9202 :=
    mul_le_mul u_lt.le a_lt.le (Real.sqrt_nonneg _) (by norm_num)
  have hc := cc_le
  rw [V_topTwo]
  unfold hh at hT ⊢
  linarith

theorem J_topTwo : J topTwo = V topTwo := by
  rw [J_eq, min_eq_right V_topTwo_lt_cap.le]

theorem J_topTwo_lt_cap : J topTwo < 1/4 := by
  rw [J_topTwo]
  exact V_topTwo_lt_cap

/-- The mask `topTwo` is the strict minimum of the capped objective. -/
theorem J_lt (s : Fin 64 → Bool) (hs : s ≠ topTwo) : J topTwo < J s := by
  rw [J_topTwo, J_eq]
  exact lt_min V_topTwo_lt_cap (V_lt s hs)

theorem J_le (s : Fin 64 → Bool) : J topTwo ≤ J s := by
  by_cases hs : s = topTwo
  · rw [hs]
  · exact (J_lt s hs).le

theorem objective_topTwo :
    selectionObjective law (1/4) 4294967296 (retained topTwo) = ENNReal.ofReal (J topTwo) :=
  objective_eq topTwo J_topTwo_lt_cap

/-- Distinct hard masks other than `topTwo` have strictly larger inner cost. -/
theorem objective_topTwo_lt (s : Fin 64 → Bool) (hs : s ≠ topTwo) :
    selectionObjective law (1/4) 4294967296 (retained topTwo) <
      selectionObjective law (1/4) 4294967296 (retained s) := by
  rw [objective_topTwo]
  calc ENNReal.ofReal (J topTwo) < ENNReal.ofReal (J s) :=
        (ENNReal.ofReal_lt_ofReal_iff ((J_nonneg _).trans_lt (J_lt s hs))).2 (J_lt s hs)
    _ = min (ENNReal.ofReal (1/4)) (selectionObjective law (1/4) 4294967296 (retained s)) :=
        (capped_eq s).symm
    _ ≤ selectionObjective law (1/4) 4294967296 (retained s) := min_le_right _ _

theorem objective_topTwo_lt_cap :
    selectionObjective law (1/4) 4294967296 (retained topTwo) < ENNReal.ofReal (1/4) := by
  rw [objective_topTwo]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 J_topTwo_lt_cap

/-- The original functional over all submeasures equals the hard minimum. -/
theorem selection_eq_topTwo :
    selection law (1/4) 4294967296 = selectionObjective law (1/4) 4294967296 (retained topTwo) := by
  have hle : selection law (1/4) 4294967296 ≤
      selectionObjective law (1/4) 4294967296 (retained topTwo) :=
    selection_le_objective (retained_le topTwo) _ _
  have hfin : selection law (1/4) 4294967296 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (selection_le_rho _ _ _)
  obtain ⟨s, hs⟩ := selection_attained
  refine le_antisymm hle ?_
  rw [objective_topTwo, ← ENNReal.ofReal_toReal hfin, hs]
  exact ENNReal.ofReal_le_ofReal (J_le s)

/-- The two largest gaps are exactly the atoms of index below two. -/
theorem atoms_top_iff (i : Fin 64) :
    ((atoms i : ℝ) = 1/2 ∨ (atoms i : ℝ) = 1/4) ↔ i.val < 2 := by
  rw [atoms_val]
  have hinj := pow_right_injective₀ (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  constructor
  · rintro (h | h)
    · have h' : (1/2 : ℝ)^(i.val+1) = (1/2 : ℝ)^1 := by rw [h]; norm_num
      have := hinj h'
      omega
    · have h' : (1/2 : ℝ)^(i.val+1) = (1/2 : ℝ)^2 := by rw [h]; norm_num
      have := hinj h'
      omega
  · intro h
    rcases (show i.val = 0 ∨ i.val = 1 by omega) with h | h <;> rw [h] <;> norm_num

theorem retained_topTwo_eq :
    retained topTwo = law.restrict {d : Gap | (d : ℝ) = 1/2 ∨ (d : ℝ) = 1/4} := by
  obtain ⟨m, hm, hmi⟩ := restrict_eq {d : Gap | (d : ℝ) = 1/2 ∨ (d : ℝ) = 1/4}
  rw [hm]
  congr 1
  funext i
  rw [Bool.eq_iff_iff, hmi i]
  change decide (i.val < 2) = true ↔ ((atoms i : ℝ) = 1/2 ∨ (atoms i : ℝ) = 1/4)
  rw [atoms_top_iff, decide_eq_true_iff]

end ThresholdHC.BandCostExample
