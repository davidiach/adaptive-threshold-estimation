
import ThresholdHC.AnytimeLower.GeometricBudget
import ThresholdHC.EntropyTailQuantile.QuantileTailBound

noncomputable section
open Real Filter
open scoped Topology
namespace ThresholdHC.AnytimeLower
open ThresholdHC.EntropyTailQuantile

def inflatedScale (δ : ℝ) (n : ℕ) : ℝ := budgetScale ((n:ℝ)/budgetInflation δ n)

theorem budgetInflation_eventually_pos (δ : ℝ) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    ∀ᶠ k in atTop, 0 < budgetInflation δ (N k) := by
  have hn : Tendsto (fun k => (N k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hl := tendsto_log_atTop.comp (tendsto_log_atTop.comp hn)
  have ht := tendsto_atTop_add_const_left atTop (log (1/δ)) hl
  exact ht.eventually (eventually_gt_atTop 0)

theorem inflatedScale_square {δ : ℝ} {n : ℕ} (hn : 0 < n) (hl : 0 < budgetInflation δ n) :
    (inflatedScale δ n)^2 = budgetInflation δ n/(n:ℝ) := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  unfold inflatedScale budgetScale
  rw [inv_pow,sq_sqrt (div_nonneg hnr.le hl.le),inv_div]

theorem inflatedScale_bound {δ : ℝ} {n : ℕ} {s L : ℝ}
    (hn : 0 < n) (hl : 0 < budgetInflation δ n) (hs : 0 < s)
    (hup : budgetInflation δ n ≤ 3*L) (hlo : L/8 ≤ (n:ℝ)*s^2) :
    inflatedScale δ n ≤ 5*s := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hi : budgetInflation δ n/(n:ℝ) ≤ 25*s^2 := by
    apply (div_le_iff₀ hnr).mpr
    nlinarith [sq_nonneg s]
  rw [← inflatedScale_square hn hl] at hi
  nlinarith

theorem dense_inflatedScale_bound {δ τ : ℝ} (hd : 0 ≤ δ ∧ δ ≤ 1/2) (hτ : 0 < τ)
    (j : ℕ → ℕ) (hm : Monotone j)
    (hj : ∀ᶠ k in atTop, (j k:ℝ) ≤ ((k:ℝ)+2)^2) :
    ∀ᶠ k in atTop,
      0 < testingBudget δ (fun i => geometricScale τ (j i)) k ∧
      0 < budgetInflation δ (testingBudget δ (fun i => geometricScale τ (j i)) k) ∧
      inflatedScale δ (testingBudget δ (fun i => geometricScale τ (j i)) k) ≤
        5*geometricScale τ (j k) := by
  let s := fun i => geometricScale τ (j i)
  have hs : ∀ k, 0 < s k := fun k => geometricScale_pos hτ (j k)
  have hsm : Antitone s := (geometricScale_antitone hτ.le).comp_monotone hm
  have hN := testingBudget_tendsto (by linarith : δ < 1) s hs hsm
  filter_upwards [testingBudget_geometric_inflation (by linarith : δ < 1) hτ j hm hj,
    testingBudget_lower hd s hs hsm,
    budgetInflation_eventually_pos δ _ hN,
    hN.eventually (eventually_gt_atTop 0)] with k hup hlo hl hn
  exact ⟨hn,hl,inflatedScale_bound hn hl (hs k) hup hlo⟩

end ThresholdHC.AnytimeLower
