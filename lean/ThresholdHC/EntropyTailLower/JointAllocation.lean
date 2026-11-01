import ThresholdHC.EntropyTailLower.PackedAllocation

noncomputable section
namespace ThresholdHC.EntropyTailLower
open Real
open scoped BigOperators

theorem normalized_capped_entropy_cost (ρ F B : ℝ) (hρ : 0 ≤ ρ) (hF : 0 < F)
    (hB : 0 < B) :
    F*min (ρ/F) (sqrt ((ρ/F)/B)) = min ρ (sqrt (ρ*F/B)) := by
  have he : F*(ρ/F) = ρ := by field_simp [hF.ne']
  have hs : F*sqrt ((ρ/F)/B) = sqrt (ρ*F/B) := by
    calc
      _ = sqrt (F^2)*sqrt ((ρ/F)/B) := by rw [sqrt_sq hF.le]
      _ = sqrt (F^2*((ρ/F)/B)) := (sqrt_mul (sq_nonneg F) _).symm
      _ = sqrt (ρ*F/B) := by congr 1; field_simp [hF.ne']
  rw [mul_min_of_nonneg _ _ hF.le,he,hs]

theorem common_allocation_coefficient (L B : ℝ) (hL : 0 ≤ L) (hB : 0 < B) :
    let q := min L (sqrt (L/B))/16384
    0 ≤ q ∧ q ≤ L/16384 ∧ q^2*B ≤ L/16384 := by
  let v := min L (sqrt (L/B))
  have hv := packed_min_cost L 1 B hL (by norm_num) hB
  simp only [mul_one] at hv
  change 0 ≤ v ∧ v ≤ L ∧ v^2*B ≤ L at hv
  change 0 ≤ v/16384 ∧ v/16384 ≤ L/16384 ∧ (v/16384)^2*B ≤ L/16384
  refine ⟨by positivity,div_le_div_of_nonneg_right hv.2.1 (by norm_num),?_⟩
  have hh : (v/16384)^2*B = (v^2*B)/268435456 := by ring
  rw [hh]
  have h := div_le_div_of_nonneg_right hv.2.2 (by norm_num : (0:ℝ) ≤ 268435456)
  nlinarith only [h,hL]

theorem packed_joint_allocation {T : Type} [Fintype T]
    (ρ B F D : ℝ) (hρ : 0 < ρ) (hB : 0 < B) (hF : 0 < F) (hD : 0 ≤ D)
    (τ s a G : T → ℝ) (hG : ∀ i, 0 < G i)
    (hs : ∀ i, 0 ≤ s i) (hsτ : ∀ i, s i ≤ τ i)
    (hscale : ∀ i, τ i/(a i)^2 ≤ G i)
    (hsat : ∀ i, (ρ/F)*(G i)^2 ≤ 4096*(τ i*s i/(a i)^2))
    (hsum : (∑ i, G i) ≤ F) (hcapture : F ≤ D*∑ i, G i) :
    ∃ θ u : T → ℝ,
      (∀ i, 0 < θ i) ∧ (∀ i, θ i ≤ τ i/4) ∧ (∑ i, θ i) ≤ ρ ∧
      (∀ i, 0 ≤ u i) ∧ (∀ i, u i ≤ θ i) ∧
      (∀ i, (u i)^2*B ≤ min (τ i*s i/(a i)^2) (θ i*G i)) ∧
      min ρ (sqrt (ρ*F/B)) ≤ 16384*D*∑ i, u i := by
  let L := ρ/F
  let v := min L (sqrt (L/B))
  let q := v/16384
  let θ := fun i => L*G i/16384
  let u := fun i => q*G i
  have hL : 0 < L := div_pos hρ hF
  have hv : 0 ≤ v := le_min hL.le (sqrt_nonneg _)
  have hq : 0 ≤ q ∧ q ≤ L/16384 ∧ q^2*B ≤ L/16384 :=
    common_allocation_coefficient L B hL.le hB
  have hθ (i) : 0 < θ i := div_pos (mul_pos hL (hG i)) (by norm_num)
  have hsaturated (i) : θ i*G i ≤ (τ i*s i/(a i)^2)/4 := by
    have h := hsat i
    change L*(G i)^2 ≤ 4096*(τ i*s i/(a i)^2) at h
    dsimp [θ]
    nlinarith only [h]
  have hθcap (i) : θ i ≤ τ i/4 := packed_rarity_cap _ _ _ _ _
    (hG i) (hs i) (hsτ i) (hscale i) (hsaturated i)
  have hsumθ : (∑ i, θ i) ≤ ρ := by
    have he : (∑ i, θ i) = (L/16384)*(∑ i, G i) := by
      simp only [θ,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hsum (show 0 ≤ L/16384 by positivity)
    have he' : (L/16384)*F = ρ/16384 := by dsimp [L]; field_simp
    rw [he'] at hh
    linarith only [hh,hρ]
  have hu (i) : 0 ≤ u i := mul_nonneg hq.1 (hG i).le
  have hucap (i) : u i ≤ θ i := by
    have h := mul_le_mul_of_nonneg_right hq.2.1 (hG i).le
    change q*G i ≤ L*G i/16384
    convert h using 1 <;> ring
  have hcostθ (i) : (u i)^2*B ≤ θ i*G i := by
    have h := mul_le_mul_of_nonneg_right hq.2.2 (sq_nonneg (G i))
    change (q*G i)^2*B ≤ (L*G i/16384)*G i
    nlinarith only [h]
  have hcost (i) : (u i)^2*B ≤ min (τ i*s i/(a i)^2) (θ i*G i) := by
    have hn : 0 ≤ θ i*G i := mul_nonneg (hθ i).le (hG i).le
    refine le_min ?_ (hcostθ i)
    nlinarith only [hcostθ i,hsaturated i,hn]
  have hfinal : min ρ (sqrt (ρ*F/B)) ≤ 16384*D*∑ i, u i := by
    rw [← normalized_capped_entropy_cost ρ F B hρ.le hF hB]
    have hh := mul_le_mul_of_nonneg_right hcapture hv
    change F*v ≤ _
    have he : D*(∑ i, G i)*v = 16384*D*∑ i, u i := by
      simp only [u,← Finset.mul_sum]
      dsimp [q]
      ring
    exact hh.trans_eq he
  exact ⟨θ,u,hθ,hθcap,hsumθ,hu,hucap,hcost,hfinal⟩

end ThresholdHC.EntropyTailLower
