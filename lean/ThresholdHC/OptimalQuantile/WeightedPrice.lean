import ThresholdHC.OptimalQuantile.Quadratic

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.OptimalQuantile
open ThresholdHC.EntropyTailQuantile

theorem root_price_iff_entropy {I : Type} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 < w i) {k d : ℝ} (hk : 0 < k) (hd : 0 ≤ d) :
    (∀ x : I → ℝ, (∀ i, 0 ≤ x i) → sqrt (costEntropy x) ≤ d+k*(∑ i, w i*x i)) ↔
      (∀ x : I → ℝ, (∀ i, 0 ≤ x i) → costEntropy x ≤ (4*k*d)*(∑ i, w i*x i)) := by
  constructor
  · intro h x hx
    let C := ∑ i, w i*x i
    have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).le (hx i))
    rcases hC.eq_or_lt with hz | hC
    · have hx0 : x = fun _ => 0 := by
        funext i
        have hp : w i*x i ≤ 0 := by
          have hh := Finset.single_le_sum (fun j _ => mul_nonneg (hw j).le (hx j)) (Finset.mem_univ i)
          change w i*x i ≤ C at hh
          rwa [← hz] at hh
        exact le_antisymm (nonpos_of_mul_nonpos_right hp (hw i)) (hx i)
      simp [hx0]
    have hs (t : ℝ) (ht : 0 ≤ t) : sqrt (t*costEntropy x) ≤ d+(k*C)*t := by
      have hh := h (fun i => t*x i) (fun i => mul_nonneg ht (hx i))
      have he : (∑ i, w i*(t*x i)) = t*C := by
        dsimp only [C]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [costEntropy_smul,he] at hh
      convert hh using 1
      ring
    have he := (scaled_root_bound_iff (costEntropy_nonneg hx) (mul_pos hk hC) hd).mp hs
    change costEntropy x ≤ (4*k*d)*C
    nlinarith only [he]
  · intro h x hx
    have hC : 0 ≤ ∑ i, w i*x i := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).le (hx i))
    apply sqrt_le_iff.mpr
    refine ⟨add_nonneg hd (mul_nonneg hk.le hC),?_⟩
    nlinarith only [h x hx,sq_nonneg (d-k*(∑ i, w i*x i))]

theorem root_price_iff_partition {I : Type} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 < w i) {k d : ℝ} (hk : 0 < k) (hd : 0 ≤ d) :
    (∀ x : I → ℝ, (∀ i, 0 ≤ x i) → sqrt (costEntropy x) ≤ d+k*(∑ i, w i*x i)) ↔
      (∑ i, exp (1-(4*k*d)*w i)) ≤ 1 :=
  (root_price_iff_entropy w hw hk hd).trans (weighted_entropy_iff_partition w (4*k*d))

end ThresholdHC.OptimalQuantile
