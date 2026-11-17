import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

noncomputable section
namespace ThresholdHC.FiniteSelectionApproximation

/-- The note's derivative bound, with a natural ceiling. -/
def logScale (R : ℝ) : ℝ := 4 + (⌈Real.logb 2 R⌉₊ : ℝ)

/-- Number of subcells in each dyadic interval. -/
def cellCount (m : ℕ) (R ε : ℝ) : ℕ := ⌈16*(m:ℝ)*logScale R/ε⌉₊

def beta (ε : ℝ) : ℝ := 1+ε/4

/-- A canonical rational upper rounding when `ε` is rational. The formal
mathematical specification does not claim verified transcendental execution. -/
def upperLog (r ε a : ℝ) : ℝ := (ε/8)*(⌈Real.log (a/r)/(ε/8)⌉₊ : ℝ)

theorem logScale_ge_four (R : ℝ) : 4 ≤ logScale R := by
  unfold logScale
  linarith [Nat.cast_nonneg (α := ℝ) ⌈Real.logb 2 R⌉₊]

theorem logScale_derivative {R : ℝ} (hR : 1 ≤ R) :
    3+Real.log R ≤ logScale R := by
  have hlog : 0 ≤ Real.log R := Real.log_nonneg hR
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo1 : Real.log 2 ≤ 1 := by
    simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
  have hb : Real.log R ≤ Real.logb 2 R := by
    rw [Real.logb, le_div_iff₀ htwo]
    exact mul_le_of_le_one_right hlog htwo1
  have hc := Nat.le_ceil (Real.logb 2 R)
  unfold logScale
  linarith

theorem cellCount_pos {m : ℕ} {R ε : ℝ} (hm : 0 < m) (hε : 0 < ε) :
    0 < cellCount m R ε := by
  have hL := logScale_ge_four R
  unfold cellCount
  apply Nat.ceil_pos.mpr
  positivity

/-- Accumulated bin error at every partial stage, with the note's constants. -/
theorem compression_error {m n : ℕ} {R ε : ℝ} (hm : 0 < m)
    (hn : n ≤ m) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let M := cellCount m R ε
    let η := (1+1/(M:ℝ))^n-1
    0 ≤ η ∧ η ≤ 1 ∧ logScale R*η ≤ ε/8 := by
  dsimp
  let M := cellCount m R ε
  let L := logScale R
  have hL : 4 ≤ L := logScale_ge_four R
  have hM : (0:ℝ) < M := Nat.cast_pos.mpr (cellCount_pos hm hε)
  have hceil : 16*(m:ℝ)*L/ε ≤ M := Nat.le_ceil _
  have hmain : 16*(m:ℝ)*L ≤ M*ε := (div_le_iff₀ hε).mp hceil
  have hnm : (n:ℝ) ≤ m := Nat.cast_le.mpr hn
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have ht0 : 0 ≤ (n:ℝ)/M := div_nonneg hn0 hM.le
  have ht : L*((n:ℝ)/M) ≤ ε/16 := by
    have hbound : (16*(n:ℝ)*L)/M ≤ ε := (div_le_iff₀ hM).mpr (by
      nlinarith [mul_nonneg (sub_nonneg.mpr hnm) (show 0 ≤ L by linarith)])
    calc
      L*((n:ℝ)/M) = ((16*(n:ℝ)*L)/M)/16 := by ring
      _ ≤ ε/16 := div_le_div_of_nonneg_right hbound (by norm_num)
  have ht1 : (n:ℝ)/M ≤ 1 := by nlinarith
  have hexp : (1+1/(M:ℝ))^n ≤ Real.exp ((n:ℝ)/M) := by
    calc
      (1+1/(M:ℝ))^n ≤ (Real.exp (1/(M:ℝ)))^n := by
        gcongr
        simpa [add_comm] using Real.add_one_le_exp (1/(M:ℝ))
      _ = Real.exp ((n:ℝ)/M) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have habs := Real.abs_exp_sub_one_le (show |(n:ℝ)/M| ≤ 1 by simpa [abs_of_nonneg ht0])
  rw [abs_of_nonneg ht0] at habs
  have heta : (1+1/(M:ℝ))^n-1 ≤ 2*((n:ℝ)/M) := by
    have := le_abs_self (Real.exp ((n:ℝ)/M)-1)
    linarith
  have heta0 : 0 ≤ (1+1/(M:ℝ))^n-1 := sub_nonneg.mpr (one_le_pow₀ (by
    have : 0 ≤ 1/(M:ℝ) := by positivity
    linarith))
  have hetaL : L*((1+1/(M:ℝ))^n-1) ≤ ε/8 := by
    nlinarith [mul_nonneg (show 0 ≤ L by linarith) (sub_nonneg.mpr heta)]
  exact ⟨heta0, by nlinarith, hetaL⟩

theorem upperLog_nonneg {r ε a : ℝ} (hε : 0 ≤ ε) : 0 ≤ upperLog r ε a := by
  unfold upperLog
  positivity

theorem upperLog_bounds {r ε a : ℝ} (hr : 0 < r) (hε : 0 < ε) (ha : r ≤ a) :
    Real.log (a/r) ≤ upperLog r ε a ∧ upperLog r ε a ≤ Real.log (a/r)+ε/8 := by
  have hd : 0 < ε/8 := by positivity
  have hlog : 0 ≤ Real.log (a/r) := Real.log_nonneg ((le_div_iff₀ hr).mpr (by simpa using ha))
  have hlo := Nat.le_ceil (Real.log (a/r)/(ε/8))
  have hhi := Nat.ceil_lt_add_one (div_nonneg hlog hd.le)
  constructor
  · have := (div_le_iff₀ hd).mp hlo
    simpa [upperLog, mul_comm] using this
  · have := (lt_div_iff₀ hd).mp (show (⌈Real.log (a/r)/(ε/8)⌉₊:ℝ)-1 < Real.log (a/r)/(ε/8) by linarith)
    unfold upperLog
    nlinarith

theorem beta_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 < beta ε ∧ (beta ε)^2 ≤ 1+ε ∧ 1+ε/2 ≤ (beta ε)^2 := by
  unfold beta
  constructor
  · linarith
  constructor <;> nlinarith [sq_nonneg ε]

end ThresholdHC.FiniteSelectionApproximation
