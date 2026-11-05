import ThresholdHC.Anytime.KnownStages

noncomputable section
open Real
namespace ThresholdHC.Anytime
open ThresholdHC.HardBudget ThresholdHC.Confidence

def logBudget (B : ℝ) : ℝ := log (1+B)/log 2
def inflation (B δ : ℝ) : ℝ := log (1/δ)+2*log (2+logBudget B)

theorem logBudget_nonneg {B : ℝ} (hB : 0 ≤ B) : 0 ≤ logBudget B :=
  div_nonneg (log_nonneg (by linarith)) (log_pos (by norm_num)).le

theorem inflation_ge_log {B δ : ℝ} (hB : 0 ≤ B) : log (1/δ) ≤ inflation B δ := by
  have h := log_nonneg (show 1 ≤ 2+logBudget B by have h := logBudget_nonneg hB; linarith)
  unfold inflation
  linarith

theorem inflation_pos {B δ : ℝ} (hB : 0 ≤ B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    0 < inflation B δ := (confidence_log_pos hd hd').trans_le (inflation_ge_log hB)

theorem count_log_bound {B : ℝ} (hB : 0 ≤ B) : (stageCount B:ℝ) ≤ logBudget B := by
  let k := stageCount B
  have hp : (paid k:ℝ) ≤ B := (Nat.cast_le.mpr (paid_fits B)).trans (Nat.floor_le hB)
  have he := congrArg (fun n : ℕ => (n:ℝ)) (paid_formula k)
  push_cast at he
  have hpow : (2:ℝ)^k ≤ 1+B := by linarith
  have hlog := log_le_log (by positivity : 0 < (2:ℝ)^k) hpow
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (log_pos (by norm_num : (1:ℝ)<2))).mpr hlog

theorem count_zero_small {B : ℝ} (_hB : 0 ≤ B) (h : stageCount B = 0) : B < 4 := by
  have hn := next_exceeds B
  rw [h] at hn
  have hh : ⌊B⌋₊+1 ≤ 4 := by simpa [paid,stageCap,stageAllowance] using Nat.succ_le_of_lt hn
  have he := Nat.lt_floor_add_one B
  exact he.trans_le (by exact_mod_cast hh)

theorem completed_stage_bounds {B : ℝ} (hB : 0 ≤ B) {j : ℕ} (hj : stageCount B = j+1) :
    (stageCap j:ℝ) ≤ B ∧ B < 4*(stageCap j:ℝ) := by
  have hf := paid_fits B
  rw [hj] at hf
  have he := (Nat.cast_le.mpr hf).trans (Nat.floor_le hB)
  have hcap : stageCap j ≤ paid (j+1) := by change stageCap j ≤ paid j+stageCap j; omega
  refine ⟨(Nat.cast_le.mpr hcap).trans he,?_⟩
  have hn := next_exceeds B
  rw [hj] at hn
  have heB : B < (paid (j+1+1):ℝ) := (Nat.lt_floor_add_one B).trans_le (by exact_mod_cast Nat.succ_le_of_lt hn)
  have hp := congrArg (fun n : ℕ => (n:ℝ)) (paid_formula (j+2))
  push_cast at hp
  have hn' : (paid (j+1+1):ℝ) < 4*(stageCap j:ℝ) := by
    simp only [stageCap,stageAllowance,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    rw [pow_add] at hp
    norm_num at hp
    linarith
  exact heB.trans hn'

theorem stage_log {δ : ℝ} (hd : 0 < δ) (j : ℕ) :
    log (1/stageFailure δ j) = log (1/δ)+log ((j:ℝ)+1)+log ((j:ℝ)+2) := by
  have hj1 : (0:ℝ) < j+1 := by positivity
  have hj2 : (0:ℝ) < j+2 := by positivity
  unfold stageFailure
  rw [one_div_div,log_div (mul_pos hj1 hj2).ne' hd.ne',log_mul hj1.ne' hj2.ne',log_div one_ne_zero hd.ne',log_one]
  ring

theorem stage_log_le {B δ : ℝ} (hB : 0 ≤ B) (hd : 0 < δ) {j : ℕ} (hj : stageCount B = j+1) :
    log (1/stageFailure δ j) ≤ inflation B δ := by
  have hn := count_log_bound hB
  rw [hj] at hn
  push_cast at hn
  have hb := logBudget_nonneg hB
  have h₁ := log_le_log (show (0:ℝ) < j+1 by positivity) (show (j:ℝ)+1 ≤ 2+logBudget B by linarith)
  have h₂ := log_le_log (show (0:ℝ) < j+2 by positivity) (show (j:ℝ)+2 ≤ 2+logBudget B by linarith)
  rw [stage_log hd]
  unfold inflation
  linarith

end ThresholdHC.Anytime
