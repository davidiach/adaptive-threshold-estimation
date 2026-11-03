import ThresholdHC.EntropyTailLower.CanonicalBands
import ThresholdHC.EntropyTailLower.DyadicMass

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.EntropyTailLower

def FiniteAllocationBound {I : Type} [Fintype I] (w t : I → ℝ) (ρ R : ℝ) : Prop :=
  ∀ r : I → ℝ, (∀ i, 0 ≤ r i) → (∀ i, r i ≤ 1/4) →
    (∑ i, w i*r i) ≤ ρ → (∑ i, w i*min (r i) (t i*sqrt (r i))) ≤ R

theorem finiteAllocationBound_restrict {I : Type} [Fintype I]
    (w t : I → ℝ) (ρ R : ℝ) (h : FiniteAllocationBound w t ρ R)
    (p : I → Prop) [DecidablePred p] :
    FiniteAllocationBound (fun i => if p i then w i else 0) t ρ R := by
  intro r hr hr4 hρ
  let q := fun i => if p i then r i else 0
  have hq (i) : 0 ≤ q i := by dsimp [q]; split_ifs; exact hr i; exact le_rfl
  have hq4 (i) : q i ≤ 1/4 := by dsimp [q]; split_ifs; exact hr4 i; norm_num
  have hm : (∑ i, w i*q i) = ∑ i, (if p i then w i else 0)*r i := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [q]
    split_ifs <;> simp
  have hc : (∑ i, w i*min (q i) (t i*sqrt (q i))) =
      ∑ i, (if p i then w i else 0)*min (r i) (t i*sqrt (r i)) := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [q]
    split_ifs <;> simp
  have hh := h q hq hq4 (by rw [hm]; exact hρ)
  rwa [hc] at hh

theorem finiteAllocationBound_dyadic_ordinary {n : ℕ} (v : Fin n → ℝ)
    (ρ c R : ℝ) (hρ : 0 < ρ) (hc : 0 ≤ c) (hv : ∀ i, 0 ≤ v i)
    (hcap : ∀ i, v i ≤ 4*ρ)
    (hsmall : ∀ i, 0 < v i → c*(2:ℝ)^(i.val+1) ≤ 1)
    (hbound : FiniteAllocationBound v (fun i => c*(2:ℝ)^(i.val+1)) ρ R) :
    c*(∑ i, v i*(2:ℝ)^(i.val+1)) ≤ 32*R := by
  obtain ⟨q,hq,hqm,hqf⟩ := dyadic_top_mass v (4*ρ) hv (by positivity) hcap
  let r := fun i => q i/16
  have hr (i) : 0 ≤ r i := div_nonneg (hq i).1 (by norm_num)
  have hr4 (i) : r i ≤ 1/4 := by dsimp [r]; linarith [(hq i).2]
  have hr1 (i) : r i ≤ 1 := by linarith [hr4 i]
  have hm : (∑ i, v i*r i) ≤ ρ := by
    have he : (∑ i, v i*r i) = (∑ i, v i*q i)/16 := by
      simp only [r,mul_div_assoc,Finset.sum_div]
    rw [he]
    linarith
  have hh := hbound r hr hr4 hm
  have hi (i : Fin n) : c*(v i*q i*(2:ℝ)^(i.val+1)) ≤
      16*(v i*min (r i) (c*(2:ℝ)^(i.val+1)*sqrt (r i))) := by
    rcases (hv i).eq_or_lt with hz | hp
    · rw [← hz]; simp
    · have ht : 0 ≤ c*(2:ℝ)^(i.val+1) := mul_nonneg hc (by positivity)
      have hl := allocation_min_linear (r i) (c*(2:ℝ)^(i.val+1)) (hr i) (hr1 i) ht
      rw [min_eq_right (hsmall i hp)] at hl
      have hm := mul_le_mul_of_nonneg_left hl (hv i)
      dsimp [r] at hm ⊢
      nlinarith only [hm]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [← Finset.mul_sum] at hs
  have htop := mul_le_mul_of_nonneg_left hqf hc
  nlinarith only [hs,htop,hh]

theorem finiteAllocationBound_ignored {I : Type} [Fintype I]
    (v t : I → ℝ) (ρ R : ℝ) (hρ : 0 ≤ ρ) (hv : ∀ i, 0 ≤ v i)
    (ht : ∀ i, 0 < v i → 1 ≤ t i)
    (hbound : FiniteAllocationBound v t ρ R) : min ρ (∑ i, v i) ≤ 4*R := by
  let V := ∑ i, v i
  have hV : 0 ≤ V := Finset.sum_nonneg (fun i _ => hv i)
  have hR : 0 ≤ R := by
    have hh := hbound (fun _ => 0) (fun _ => le_rfl) (fun _ => by norm_num) (by simpa using hρ)
    simpa using hh
  by_cases hz : V = 0
  · change min ρ V ≤ 4*R
    rw [hz,min_eq_right hρ]
    positivity
  · have hVp : 0 < V := lt_of_le_of_ne hV (Ne.symm hz)
    let r := min ρ V/(4*V)
    have hr : 0 ≤ r := div_nonneg (le_min hρ hV) (by positivity)
    have hr4 : r ≤ 1/4 := by
      apply (div_le_iff₀ (show 0 < 4*V by positivity)).mpr
      nlinarith only [min_le_right ρ V]
    have hr1 : r ≤ 1 := by linarith
    have hm : (∑ i, v i*r) = min ρ V/4 := by
      rw [← Finset.sum_mul]
      change V*(min ρ V/(4*V)) = min ρ V/4
      field_simp
    have hcost (i) : v i*r ≤ v i*min r (t i*sqrt r) := by
      rcases (hv i).eq_or_lt with hz | hp
      · rw [← hz]; simp
      · have ht' := ht i hp
        have hl := allocation_min_linear r (t i) hr hr1 (by linarith)
        rw [min_eq_left ht',mul_one] at hl
        exact mul_le_mul_of_nonneg_left hl (hv i)
    have hb := hbound (fun _ => r) (fun _ => hr) (fun _ => hr4)
      (by rw [hm]; have hh := min_le_left ρ V; linarith)
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcost i)
    rw [hm] at hs
    change min ρ V ≤ 4*R
    linarith

open MeasureTheory ThresholdHC.Tier6 ThresholdHC.StoppingProgram

theorem certificate_canonical_finiteAllocationBound {I : Type} [Fintype I] {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hB : 0 < B) (hN : 0 < N)
    (C : Certificate N) (hC : Feasible μ ρ B C)
    (j : I → ℕ) (hj : Function.Injective j) (hlow : ∀ i, 6 ≤ j i) :
    FiniteAllocationBound (fun i => μ.real (ThresholdHC.EntropyTail.band (j i)))
      (fun i => 1/(sqrt B*((1/2:ℝ)^(j i+1)))) ρ
      (256*C.bias+sqrt ((4294967296*exp 48)*C.variance)) := by
  intro r hr hr4 hρ
  have hh := certificate_canonical_band_allocation_nonneg μ ρ B hB hN C hC j hj hlow r hr hr4 hρ
  have he (i) : sqrt (r i/(B*((1/2:ℝ)^(j i+1))^2)) =
      (1/(sqrt B*((1/2:ℝ)^(j i+1))))*sqrt (r i) :=
    sqrt_allocation_cost (r i) B _ (hr i) hB (by positivity)
  simpa only [he] using hh

theorem canonical_inverse_scale (B : ℝ) (hB : 0 < B) (j : ℕ) :
    1/(sqrt B*((1/2:ℝ)^(j+1))) = (1/sqrt B)*(2:ℝ)^(j+1) := by
  have hs : sqrt B ≠ 0 := (sqrt_pos.mpr hB).ne'
  rw [div_pow,one_pow]
  field_simp [hs]

end ThresholdHC.EntropyTailLower
