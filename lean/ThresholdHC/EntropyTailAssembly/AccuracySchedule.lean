import ThresholdHC.EntropyTailAssembly.ErrorCaps
import Mathlib.Analysis.SpecificLimits.Normed

/-! Geometric accuracy and likelihood-bank allowances. -/

noncomputable section
open MeasureTheory Set Real Filter
open scoped BigOperators Topology

namespace ThresholdHC.EntropyTailAssembly
open ThresholdHC.Tier6

def levelAccuracy (ρ : ℝ) (l : ℕ) : ℝ := ρ*(1/16:ℝ)^(l+1)
def levelEpsilon (l : ℕ) : ℝ := (1/64:ℝ)*(1/16:ℝ)^l

theorem levelAccuracy_pos {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ) : 0 < levelAccuracy ρ l := by
  unfold levelAccuracy
  positivity

theorem levelAccuracy_succ (ρ : ℝ) (l : ℕ) : levelAccuracy ρ (l+1) = levelAccuracy ρ l/16 := by
  unfold levelAccuracy
  rw [pow_succ]
  ring

theorem levelAccuracy_zero (ρ : ℝ) : levelAccuracy ρ 0 = ρ/16 := by
  unfold levelAccuracy
  norm_num
  ring

theorem levelAccuracy_le_first {ρ : ℝ} (hρ : 0 ≤ ρ) (l : ℕ) : levelAccuracy ρ l ≤ ρ/16 := by
  rw [← levelAccuracy_zero]
  unfold levelAccuracy
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hρ

theorem levelEpsilon_pos (l : ℕ) : 0 < levelEpsilon l := by unfold levelEpsilon; positivity

theorem levelEpsilon_le_one (l : ℕ) : levelEpsilon l ≤ 1 := by
  have h : (1/16:ℝ)^l ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold levelEpsilon
  linarith

theorem levelEpsilon_accuracy (ρ : ℝ) (l : ℕ) : ρ*levelEpsilon l = levelAccuracy ρ l/4 := by
  unfold levelEpsilon levelAccuracy
  rw [pow_succ]
  ring

theorem levelEpsilon_log (l : ℕ) : log (levelEpsilon l)⁻¹ ≤ 6+4*l := by
  have he : (levelEpsilon l)⁻¹ = 64*(16:ℝ)^l := by
    unfold levelEpsilon
    simp [mul_inv_rev, one_div, mul_comm]
  rw [he, log_mul (by norm_num) (by positivity), log_pow]
  have hl2 : log (2:ℝ) ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have h64 : log (64:ℝ) = 6*log 2 := by
    rw [show (64:ℝ) = 2^6 by norm_num, log_pow]; norm_num
  have h16 : log (16:ℝ) = 4*log 2 := by
    rw [show (16:ℝ) = 2^4 by norm_num, log_pow]; norm_num
  rw [h64, h16]
  nlinarith [mul_le_mul_of_nonneg_left hl2 (show (0:ℝ) ≤ l by positivity)]

theorem sqrt_levelAccuracy {ρ : ℝ} (hρ : 0 ≤ ρ) (l : ℕ) :
    sqrt (levelAccuracy ρ l) = sqrt ρ*(1/4:ℝ)^(l+1) := by
  have he : (1/16:ℝ)^(l+1) = ((1/4:ℝ)^(l+1))^2 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  rw [levelAccuracy, he, sqrt_mul hρ, sqrt_sq (by positivity)]

theorem fourthRoot_levelAccuracy {ρ : ℝ} (hρ : 0 ≤ ρ) (l : ℕ) :
    sqrt (sqrt (levelAccuracy ρ l)) = sqrt (sqrt ρ)*(1/2:ℝ)^(l+1) := by
  have he : (1/4:ℝ)^(l+1) = ((1/2:ℝ)^(l+1))^2 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  rw [sqrt_levelAccuracy hρ, he, sqrt_mul (sqrt_nonneg ρ), sqrt_sq (by positivity)]

theorem levelAccuracy_tendsto (ρ : ℝ) : Tendsto (levelAccuracy ρ) atTop (𝓝 0) := by
  change Tendsto (fun l => ρ*(1/16:ℝ)^(l+1)) atTop (𝓝 0)
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ) ≤ 1/16) (by norm_num : (1/16:ℝ) < 1)).mul_const (1/16:ℝ)
  simpa [levelAccuracy, pow_succ] using h.const_mul ρ

theorem exists_terminal_level {ρ z : ℝ} (_hρ : 0 < ρ) (hz : 0 < z) (hzρ : z ≤ ρ/128) :
    ∃ J : ℕ, 8*z ≤ levelAccuracy ρ J ∧ levelAccuracy ρ J < 128*z := by
  have hex : ∃ k, levelAccuracy ρ k < 8*z :=
    ((levelAccuracy_tendsto ρ).eventually (gt_mem_nhds (by positivity : (0:ℝ) < 8*z))).exists
  let k := Nat.find hex
  have hk := Nat.find_spec hex
  change levelAccuracy ρ k < 8*z at hk
  have hk0 : 0 < k := by
    by_contra hn
    have he : k = 0 := by omega
    rw [he, levelAccuracy_zero] at hk
    linarith
  have hp : 8*z ≤ levelAccuracy ρ (k-1) :=
    le_of_not_gt (Nat.find_min hex (show k-1 < k by omega))
  refine ⟨k-1, hp, ?_⟩
  have he : k = (k-1)+1 := by omega
  rw [he, levelAccuracy_succ] at hk
  linarith

theorem schedule_caps_strict (ξ : Measure Gap) [IsFiniteMeasure ξ] {ρ : ℝ}
    (hρ : 0 < ρ) (hm : ρ/128 < ξ.real univ) :
    StrictMono (fun l => errorCapExponent ξ (levelAccuracy ρ l) (levelAccuracy_pos hρ l)) := by
  apply strictMono_nat_of_lt_succ
  intro l
  apply errorCapExponent_strict ξ (levelAccuracy_pos hρ l) (levelAccuracy_pos hρ (l+1))
  · have h := levelAccuracy_le_first hρ.le l
    linarith
  · exact (levelAccuracy_succ ρ l).le

end ThresholdHC.EntropyTailAssembly
