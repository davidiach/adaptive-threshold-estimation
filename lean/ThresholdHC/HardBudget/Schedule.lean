import ThresholdHC.HardBudget.Execution

noncomputable section
namespace ThresholdHC.HardBudget

theorem paid_formula (k : ℕ) : paid k+4 = 4*2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [paid,stageCap,stageAllowance,pow_succ]; omega

theorem paid_checkpoint (j : ℕ) : paid (j+1) = reservation j := by
  have h := paid_formula (j+1)
  have hp : 0 < (2:ℕ)^(j+1) := by positivity
  unfold reservation
  omega

theorem paid_strict : StrictMono paid := by
  apply strictMono_nat_of_lt_succ
  intro n
  change paid n < paid n+4*2^n
  have : 0 < (2:ℕ)^n := by positivity
  omega

theorem index_le_paid (n : ℕ) : n ≤ paid n := by
  induction n with
  | zero => rfl
  | succ n ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (paid_strict (Nat.lt_succ_self _)))

def stageCount (B : ℝ) : ℕ := Nat.findGreatest (fun k => paid k ≤ ⌊B⌋₊) ⌊B⌋₊

theorem paid_fits (B : ℝ) : paid (stageCount B) ≤ ⌊B⌋₊ :=
  Nat.findGreatest_spec (P := fun k => paid k ≤ ⌊B⌋₊) (Nat.zero_le _) (Nat.zero_le _ : paid 0 ≤ _)

theorem next_exceeds (B : ℝ) : ⌊B⌋₊ < paid (stageCount B+1) := by
  by_contra! h
  have h' := Nat.le_findGreatest (P := fun k => paid k ≤ ⌊B⌋₊)
    ((index_le_paid (stageCount B+1)).trans h) h
  change stageCount B+1 ≤ stageCount B at h'
  omega

theorem count_at_checkpoint {B : ℝ} (hB : 0 ≤ B) (m : ℕ) (hl : (reservation m : ℝ) ≤ B)
    (hu : B < reservation (m+1)) : stageCount B = m+1 := by
  rw [← paid_checkpoint] at hl hu
  have hl' := (Nat.le_floor_iff hB).mpr hl
  have hu' : ⌊B⌋₊ < paid (m+1+1) := by
    by_contra! h; exact hu.not_ge ((Nat.le_floor_iff hB).mp h)
  have h := paid_fits B
  have hn := next_exceeds B
  have hlow := paid_strict.lt_iff_lt.mp (lt_of_le_of_lt hl' hn)
  have hhigh := paid_strict.lt_iff_lt.mp (lt_of_le_of_lt h hu')
  omega

theorem count_zero_of_small {B : ℝ} (hB : 0 ≤ B) (hb : B < 4) : stageCount B = 0 := by
  by_contra! hn
  have h := (paid_strict.monotone (show 1 ≤ stageCount B by omega)).trans (paid_fits B)
  have h' := (Nat.le_floor_iff hB).mp h
  norm_num [paid,stageCap,stageAllowance] at h'
  linarith

end ThresholdHC.HardBudget
