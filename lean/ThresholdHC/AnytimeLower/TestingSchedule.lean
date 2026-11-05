
import ThresholdHC.AnytimeLower.FrequentTesting
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open Real Filter
open scoped Topology
namespace ThresholdHC.AnytimeLower

def testingBudget (δ : ℝ) (s : ℕ → ℝ) (k : ℕ) : ℕ :=
  ⌊((1-δ)/2)*log ((k:ℝ)+2)/(s k)^2⌋₊

theorem shifted_log_nonneg (k : ℕ) : 0 ≤ log ((k:ℝ)+2) :=
  log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) k; linarith)

theorem testingBudget_mono {δ : ℝ} (hd : δ < 1)
    (s : ℕ → ℝ) (hs : ∀ k, 0 < s k) (hm : Antitone s) : Monotone (testingBudget δ s) := by
  intro i j hij
  apply Nat.floor_le_floor
  have hl : log ((i:ℝ)+2) ≤ log ((j:ℝ)+2) :=
    log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 2)
  have hc : 0 ≤ (1-δ)/2 := by linarith
  have hp : (s j)^2 ≤ (s i)^2 := pow_le_pow_left₀ (hs j).le (hm hij) 2
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl hc) (sq_nonneg _)).trans
    (div_le_div_of_nonneg_left (mul_nonneg hc (shifted_log_nonneg j)) (sq_pos_of_pos (hs j)) hp)

theorem testingBudget_information {δ : ℝ} (hd : δ < 1)
    (s : ℕ → ℝ) (hs : ∀ k, 0 < s k) (k : ℕ) :
    (testingBudget δ s k:ℝ)*(s k)^2 ≤ ((1-δ)/2)*log ((k:ℝ)+2) := by
  exact (le_div_iff₀ (sq_pos_of_pos (hs k))).mp
    (Nat.floor_le (div_nonneg (mul_nonneg (by linarith) (shifted_log_nonneg k)) (sq_nonneg _)))

theorem testingBudget_not_summable {δ : ℝ} (hd : δ < 1)
    (s : ℕ → ℝ) (hs : ∀ k, 0 < s k) :
    ¬Summable (fun k => exp (-((testingBudget δ s k:ℝ)*(s k)^2)/(1-δ))) := by
  intro h
  apply not_summable_half_log
  apply h.of_nonneg_of_le (fun k => (exp_pos _).le)
  intro k
  apply exp_le_exp.mpr
  apply (le_div_iff₀ (by linarith : 0 < 1-δ)).mpr
  have hi := testingBudget_information hd s hs k
  nlinarith

theorem testingBudget_tendsto {δ : ℝ} (hd : δ < 1)
    (s : ℕ → ℝ) (hs : ∀ k, 0 < s k) (hm : Antitone s) :
    Tendsto (testingBudget δ s) atTop atTop := by
  have hl : Tendsto (fun k : ℕ => log ((k:ℝ)+2)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_atTop_add_const_right atTop (2:ℝ) tendsto_natCast_atTop_atTop)
  apply tendsto_atTop.mpr
  intro n
  have he := hl.eventually (eventually_ge_atTop ((n:ℝ)*(s 0)^2/((1-δ)/2)))
  apply he.mono
  intro k hk
  apply Nat.le_floor
  apply (le_div_iff₀ (sq_pos_of_pos (hs k))).mpr
  have hsq : (s k)^2 ≤ (s 0)^2 := pow_le_pow_left₀ (hs k).le (hm (Nat.zero_le k)) 2
  have hb := (div_le_iff₀ (by linarith : 0 < (1-δ)/2)).mp hk
  nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α:=ℝ) n)]

end ThresholdHC.AnytimeLower
