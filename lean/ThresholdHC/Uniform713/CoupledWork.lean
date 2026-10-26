import ThresholdHC.Uniform713.Specification

/-! The cost in the full theorem is the actual number of distinct observations
used by two classifiers sharing their dyadic prefix stream. -/

noncomputable section
namespace ThresholdHC.Uniform713

/-- Coupled cost: one observation at level zero; the larger of the two stopping
costs for a fine/coarse increment at every subsequent level. -/
def coupledLevelWork {Ω : Type*} (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 1
  | l+1, ω => max (levelWork X (l+1) ω) (levelWork X l ω)

@[simp] theorem levelWork_zero {Ω : Type*} (X : ℕ → Ω → ℝ) (ω : Ω) :
    levelWork X 0 ω = 1 := by
  have hs := Nat.eq_zero_of_le_zero (stopLevel_le (fun k => dyadicMean X k ω) 0)
  unfold levelWork work
  rw [hs,cap_zero]

theorem levelWork_succ_eq_max {Ω : Type*} (X : ℕ → Ω → ℝ) (l : ℕ) (ω : Ω) :
    levelWork X (l+1) ω = max (levelWork X (l+1) ω) (levelWork X l ω) := by
  exact (max_eq_left (work_mono (fun k => dyadicMean X k ω) (Nat.le_succ l))).symm

theorem coupledLevelWork_eq_levelWork {Ω : Type*} (X : ℕ → Ω → ℝ) (l : ℕ) (ω : Ω) :
    coupledLevelWork X l ω = levelWork X l ω := by
  cases l with
  | zero => simp [coupledLevelWork]
  | succ l => exact (levelWork_succ_eq_max X l ω).symm

theorem uniformWork_eq_coupled {Θ Ω : Type*} (X : ℕ → Ω → ℝ) (x : Θ × (ℕ × Ω)) :
    uniformWork X x = coupledLevelWork X x.2.1 x.2.2 := by
  exact (coupledLevelWork_eq_levelWork X x.2.1 x.2.2).symm

end ThresholdHC.Uniform713
