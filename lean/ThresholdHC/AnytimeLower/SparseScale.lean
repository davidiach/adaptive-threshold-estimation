import ThresholdHC.AnytimeLower.SparseGeometry

noncomputable section
open Real Filter
open scoped Topology
namespace ThresholdHC.AnytimeLower

theorem geometricScale_cancel {τ : ℝ} (hτ : 0 < τ) (j : ℕ) :
    ((16:ℝ)^j/τ^2)*(geometricScale τ j)^2 = 1 := by
  rw [← geometricScale_inverse_square hτ]
  exact one_div_mul_cancel (sq_pos_of_pos (geometricScale_pos hτ j)).ne'

theorem sparseBudget_scale_lower {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (j : ℕ) :
    (16:ℝ)^(sparseOffset j) ≤ (sparseBudget τ j:ℝ)*(geometricScale τ j)^2 := by
  have hb := mul_le_mul_of_nonneg_right (sparseBudget_bounds hτ hτ1 j).1
    (sq_nonneg (geometricScale τ j))
  have he : ((16:ℝ)^(sparseIndex j)/τ^2)*(geometricScale τ j)^2 =
      (16:ℝ)^(sparseOffset j) := by
    rw [sparseIndex,pow_add]
    calc
      _ = (((16:ℝ)^j/τ^2)*(geometricScale τ j)^2)*(16:ℝ)^(sparseOffset j) := by ring
      _ = _ := by rw [geometricScale_cancel hτ,one_mul]
  exact he ▸ hb

theorem sparseBudget_scale_upper {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (j : ℕ) :
    (sparseBudget τ j:ℝ)*(geometricScale τ (sparseIndex j+1))^2 ≤ 1/8 := by
  have hb := mul_le_mul_of_nonneg_right (sparseBudget_bounds hτ hτ1 j).2
    (sq_nonneg (geometricScale τ (sparseIndex j+1)))
  have he : geometricScale τ (sparseIndex j+1) = geometricScale τ (sparseIndex j)/4 := by
    simp only [geometricScale,pow_succ]
    ring
  rw [he] at hb
  have hc := geometricScale_cancel hτ (sparseIndex j)
  have hid : 2*((16:ℝ)^(sparseIndex j)/τ^2)*(geometricScale τ (sparseIndex j)/4)^2 = 1/8 := by
    calc
      _ = (((16:ℝ)^(sparseIndex j)/τ^2)*(geometricScale τ (sparseIndex j))^2)/8 := by ring
      _ = _ := by rw [hc]
  simpa only [he] using hb.trans_eq hid

theorem sparse_inflatedScale_bound {δ τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∀ᶠ j : ℕ in atTop, 0 < sparseBudget τ j ∧
      0 < budgetInflation δ (sparseBudget τ j) ∧
      inflatedScale δ (sparseBudget τ j) ≤ geometricScale τ j := by
  filter_upwards [sparseBudget_inflation (δ:=δ) hτ hτ1,eventually_ge_atTop 64] with j hj h64
  have hn : 0 < sparseBudget τ j := Nat.ceil_pos.mpr (by positivity)
  have hnr : (0:ℝ) < sparseBudget τ j := by exact_mod_cast hn
  have hu := (hj.2.trans (sparseOffset_power h64)).trans (sparseBudget_scale_lower hτ hτ1 j)
  have hs : (inflatedScale δ (sparseBudget τ j))^2 ≤ (geometricScale τ j)^2 := by
    rw [inflatedScale_square hn hj.1]
    exact (div_le_iff₀ hnr).mpr (by simpa only [mul_comm] using hu)
  refine ⟨hn,hj.1,?_⟩
  nlinarith [geometricScale_pos hτ j]

end ThresholdHC.AnytimeLower
