import ThresholdHC.ArbitraryLawAdaptation.TailPilot
import ThresholdHC.Anytime.Schedule

/-! The fixed, law-independent pilot schedule of the arbitrary-law ladder. -/

noncomputable section
set_option autoImplicit false
open Real
namespace ThresholdHC.ArbitraryLawController
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.HardBudget ThresholdHC.Anytime

def pilotLog (δ : ℝ) (s J : ℕ) : ℝ :=
  log (4 * (J : ℝ) / stageFailure δ s) / log 2

def pilotGroups (δ : ℝ) (s J : ℕ) : ℕ := ⌈pilotLog δ s J⌉₊

def repetitions (δ : ℝ) (s J : ℕ) : ℕ := 8 * pilotGroups δ s J + 1

def pilotReservation (δ : ℝ) (s J : ℕ) : ℕ := repetitions δ s J * pilotSpan J

def depth (δ : ℝ) (s : ℕ) : ℕ :=
  Nat.findGreatest (fun J => 2 * pilotReservation δ s J ≤ stageCap s) (s + 2)

def remaining (δ : ℝ) (s : ℕ) : ℕ := stageCap s - pilotReservation δ s (depth δ s)

theorem repetitions_pos (δ : ℝ) (s J : ℕ) : 0 < repetitions δ s J := by
  unfold repetitions
  omega

theorem repetitions_odd (δ : ℝ) (s J : ℕ) :
    repetitions δ s J = 2 * (4 * pilotGroups δ s J) + 1 := by
  unfold repetitions
  omega

theorem pilotReservation_zero (δ : ℝ) (s : ℕ) : pilotReservation δ s 0 = 0 := by
  simp [pilotReservation, pilotSpan]

theorem depth_le (δ : ℝ) (s : ℕ) : depth δ s ≤ s + 2 := Nat.findGreatest_le _

theorem depth_fits (δ : ℝ) (s : ℕ) :
    2 * pilotReservation δ s (depth δ s) ≤ stageCap s := by
  apply Nat.findGreatest_spec (P := fun J => 2 * pilotReservation δ s J ≤ stageCap s)
    (m := 0) (by omega)
  simp [pilotReservation_zero]

theorem fitting_depth_le {δ : ℝ} {s J : ℕ} (hJ : 1 ≤ J)
    (hfit : 2 * pilotReservation δ s J ≤ stageCap s) : J ≤ s + 2 := by
  have hpow : 4 ^ J ≤ stageCap s := by
    have hspan := le_two_mul_pilotSpan hJ
    have hm : 1 ≤ repetitions δ s J := repetitions_pos δ s J
    dsimp [pilotReservation] at hfit
    nlinarith
  have hp : 2 ^ J ≤ 2 ^ (s + 2) := by
    calc 2 ^ J ≤ 4 ^ J := Nat.pow_le_pow_left (by omega) J
         _ ≤ stageCap s := hpow
         _ = 2 ^ (s + 2) := by simp [stageCap, stageAllowance, pow_add]; omega
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hp

theorem depth_maximal {δ : ℝ} {s J : ℕ} (hJ : 1 ≤ J)
    (hfit : 2 * pilotReservation δ s J ≤ stageCap s) : J ≤ depth δ s :=
  Nat.le_findGreatest (fitting_depth_le hJ hfit) hfit

theorem next_depth_exceeds (δ : ℝ) (s : ℕ) :
    stageCap s < 2 * pilotReservation δ s (depth δ s + 1) := by
  by_contra! h
  have := depth_maximal (by omega : 1 ≤ depth δ s + 1) h
  omega

theorem depth_zero_iff (δ : ℝ) (s : ℕ) : depth δ s = 0 ↔
    ∀ J, 1 ≤ J → stageCap s < 2 * pilotReservation δ s J := by
  constructor
  · intro hz J hJ
    by_contra! h
    have := depth_maximal hJ h
    omega
  · intro h
    by_contra! hz
    exact (h _ (by omega)).not_ge (depth_fits δ s)

theorem remaining_bounds (δ : ℝ) (s : ℕ) :
    0 < remaining δ s ∧ stageCap s ≤ 2 * remaining δ s ∧
      pilotReservation δ s (depth δ s) + remaining δ s = stageCap s := by
  have hf := depth_fits δ s
  have hc : 0 < stageCap s := by unfold stageCap stageAllowance; positivity
  unfold remaining
  omega

theorem pilot_scale_upper {δ : ℝ} {s J : ℕ} (hJ : 1 ≤ J) :
    pilotReservation δ s J ≤ repetitions δ s J * 4 ^ J :=
  Nat.mul_le_mul_left _ (pilotSpan_le hJ)

theorem pilot_scale_lower {δ : ℝ} {s J : ℕ} (hJ : 1 ≤ J) :
    repetitions δ s J * 4 ^ J ≤ 2 * pilotReservation δ s J := by
  have := Nat.mul_le_mul_left (repetitions δ s J) (le_two_mul_pilotSpan hJ)
  simpa [pilotReservation, Nat.mul_assoc, Nat.mul_left_comm] using this

end ThresholdHC.ArbitraryLawController
