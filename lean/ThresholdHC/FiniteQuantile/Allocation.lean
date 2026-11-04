import ThresholdHC.EntropyTailLower.JointAllocation

/-! Allocate rarity in proportion to the entropy actually captured after
filtering and trimming. The stronger gap filter permits this full allocation.
The loss in a variance bound is then the square root of the capture factor. -/
noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.FiniteQuantile
open ThresholdHC.EntropyTailLower

theorem full_rarity_allocation {I : Type} [Fintype I] (G τ s a : I → ℝ)
    {ρ B F : ℝ} (hρ : 0 < ρ) (hB : 0 < B) (hF : 0 < F)
    (hG : ∀ i, 0 < G i) (hs : ∀ i, 0 ≤ s i) (hτ : ∀ i, s i ≤ τ i)
    (hscale : ∀ i, τ i/(a i)^2 ≤ G i)
    (hcapture : F ≤ 65536 * ∑ i, G i)
    (hsep : ∀ i, (65536:ℝ)^2*(ρ/F)*(G i)^2 ≤ 4096*(τ i*s i/(a i)^2)) :
    ∃ θ u : I → ℝ, (∀ i, 0 < θ i) ∧ (∀ i, θ i ≤ τ i/4) ∧
      (∑ i, θ i) = ρ ∧ (∀ i, 0 ≤ u i) ∧ (∀ i, u i ≤ θ i) ∧
      (∀ i, (u i)^2*B ≤ min (τ i*s i/(a i)^2) (θ i*G i)) ∧
      min ρ (sqrt (ρ*F/B)) ≤ 256*∑ i, u i := by
  let S := ∑ i, G i
  change F ≤ 65536*S at hcapture
  have hS : 0 < S := by linarith
  let L := ρ/S
  let θ := fun i => L*G i
  let v := min L (sqrt (L/B))
  let u := fun i => v*G i
  have hL : 0 < L := div_pos hρ hS
  have hLF : L ≤ 65536*(ρ/F) := by
    rw [show 65536*(ρ/F) = (65536*ρ)/F by ring]
    apply (div_le_div_iff₀ hS hF).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hcapture hρ.le]
  have hsatur (i) : θ i*G i ≤ (τ i*s i/(a i)^2)/4 := by
    have h := hsep i
    have hh := mul_le_mul_of_nonneg_right hLF (sq_nonneg (G i))
    have hn := mul_nonneg (div_nonneg hρ.le hF.le) (sq_nonneg (G i))
    dsimp only [θ]
    nlinarith only [h, hh, hn]
  have hv := packed_min_cost L 1 B hL.le (by norm_num) hB
  simp only [mul_one] at hv
  change 0 ≤ v ∧ v ≤ L ∧ v^2*B ≤ L at hv
  have hsum : ∑ i, θ i = ρ := by
    change (∑ i, L*G i) = ρ
    rw [← Finset.mul_sum]
    exact div_mul_cancel₀ _ hS.ne'
  refine ⟨θ, u, fun i => mul_pos hL (hG i),
    fun i => packed_rarity_cap _ _ _ _ _ (hG i) (hs i) (hτ i) (hscale i) (hsatur i),
    hsum, fun i => mul_nonneg hv.1 (hG i).le,
    fun i => mul_le_mul_of_nonneg_right hv.2.1 (hG i).le, ?_, ?_⟩
  · intro i
    have hh := mul_le_mul_of_nonneg_right hv.2.2 (sq_nonneg (G i))
    have hcost : (u i)^2*B ≤ θ i*G i := by dsimp only [u, θ]; nlinarith only [hh]
    have hn : 0 ≤ θ i*G i := mul_nonneg (mul_nonneg hL.le (hG i).le) (hG i).le
    exact le_min (by linarith only [hcost, hn, hsatur i]) hcost
  · have hu : ∑ i, u i = min ρ (sqrt (ρ*S/B)) := by
      calc
        _ = S*v := by change (∑ i, v*G i) = S*v; rw [← Finset.mul_sum, mul_comm]
        _ = _ := normalized_capped_entropy_cost ρ S B hρ.le hS hB
    rw [hu]
    have hroot : sqrt (ρ*F/B) ≤ 256 * sqrt (ρ*S/B) := by
      have hh := mul_le_mul_of_nonneg_left hcapture (div_nonneg hρ.le hB.le)
      have hb : ρ*F/B ≤ 65536*(ρ*S/B) := by convert hh using 1 <;> ring
      have hp := sqrt_le_sqrt hb
      rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 65536)] at hp
      norm_num at hp
      exact hp
    rcases le_total ρ (sqrt (ρ*S/B)) with hl | hr
    · rw [min_eq_left hl]
      linarith only [min_le_left ρ (sqrt (ρ*F/B)), hρ]
    · rw [min_eq_right hr]
      exact (min_le_right _ _).trans hroot

end ThresholdHC.FiniteQuantile
