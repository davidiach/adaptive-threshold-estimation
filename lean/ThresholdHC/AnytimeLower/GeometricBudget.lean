
import ThresholdHC.AnytimeLower.LogSchedule
import ThresholdHC.AnytimeLower.TailLimits

noncomputable section
open Real Filter
open scoped Topology
namespace ThresholdHC.AnytimeLower

theorem geometricScale_inverse_square {τ : ℝ} (hτ : 0 < τ) (j : ℕ) :
    1/(geometricScale τ j)^2 = (16:ℝ)^j/τ^2 := by
  unfold geometricScale
  rw [mul_pow,← pow_mul,show j*2=2*j by omega,pow_mul]
  norm_num
  rw [div_pow,one_pow]
  field_simp

theorem testingBudget_geometric_upper {δ τ : ℝ} (hd : δ < 1) (hτ : 0 < τ)
    (j : ℕ → ℕ) (k : ℕ) :
    (testingBudget δ (fun i => geometricScale τ (j i)) k:ℝ) ≤
      ((1-δ)/(2*τ^2))*(16:ℝ)^(j k)*((k:ℝ)+2) := by
  have hs := geometricScale_pos hτ (j k)
  have hi := Nat.floor_le (div_nonneg
    (mul_nonneg (by linarith : 0 ≤ (1-δ)/2) (shifted_log_nonneg k)) (sq_nonneg (geometricScale τ (j k))))
  change (testingBudget δ (fun i => geometricScale τ (j i)) k:ℝ) ≤ _ at hi
  have he : ((1-δ)/2)*log ((k:ℝ)+2)/(geometricScale τ (j k))^2 =
      ((1-δ)/(2*τ^2))*(16:ℝ)^(j k)*log ((k:ℝ)+2) := by
    calc
      _ = ((1-δ)/2)*log ((k:ℝ)+2)*(1/(geometricScale τ (j k))^2) := by ring
      _ = _ := by rw [geometricScale_inverse_square hτ]; ring
  rw [he] at hi
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (log_le_sub_one_of_pos (by positivity : 0 < (k:ℝ)+2)).trans (by linarith)

theorem testingBudget_geometric_inflation {δ τ : ℝ} (hd : δ < 1) (hτ : 0 < τ)
    (j : ℕ → ℕ) (hm : Monotone j)
    (hj : ∀ᶠ k in atTop, (j k:ℝ) ≤ ((k:ℝ)+2)^2) :
    ∀ᶠ k in atTop, budgetInflation δ (testingBudget δ (fun i => geometricScale τ (j i)) k) ≤
      3*log ((k:ℝ)+2) := by
  apply geometric_inflation_eventually δ ((1-δ)/(2*τ^2)) (by positivity) j _
    hj (testingBudget_tendsto hd _ (fun k => geometricScale_pos hτ (j k))
      ((geometricScale_antitone hτ.le).comp_monotone hm))
  exact testingBudget_geometric_upper hd hτ j

theorem testingBudget_lower {δ : ℝ} (hd : 0 ≤ δ ∧ δ ≤ 1/2)
    (s : ℕ → ℝ) (hs : ∀ k, 0 < s k) (hm : Antitone s) :
    ∀ᶠ k : ℕ in atTop, log ((k:ℝ)+2)/8 ≤
      (testingBudget δ s k:ℝ)*(s k)^2 := by
  have ht := testingBudget_tendsto (by linarith : δ < 1) s hs hm
  filter_upwards [ht.eventually (eventually_ge_atTop 1)] with k hk
  have hn : (1:ℝ) ≤ testingBudget δ s k := by exact_mod_cast hk
  have hf := Nat.lt_floor_add_one (((1-δ)/2)*log ((k:ℝ)+2)/(s k)^2)
  change _ < (testingBudget δ s k:ℝ)+1 at hf
  have hp : ((1-δ)/2)*log ((k:ℝ)+2) <
      ((testingBudget δ s k:ℝ)+1)*(s k)^2 := (div_lt_iff₀ (sq_pos_of_pos (hs k))).mp hf
  have hquad : (s k)^2 ≤ (testingBudget δ s k:ℝ)*(s k)^2 :=
    le_mul_of_one_le_left (sq_nonneg _) hn
  have hc : log ((k:ℝ)+2)/4 ≤ ((1-δ)/2)*log ((k:ℝ)+2) := by
    nlinarith [shifted_log_nonneg k,mul_nonneg (show 0 ≤ 1/2-δ by linarith) (shifted_log_nonneg k)]
  nlinarith

end ThresholdHC.AnytimeLower
