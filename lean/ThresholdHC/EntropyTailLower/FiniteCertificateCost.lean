import ThresholdHC.EntropyTailLower.OptimalRetained
import ThresholdHC.EntropyTailLower.FiniteSelectionLift
import ThresholdHC.EntropyTailLower.GlobalCosts

noncomputable section
namespace ThresholdHC.EntropyTailLower
open MeasureTheory Real ThresholdHC.EntropyTailQuantile
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram
open scoped BigOperators ENNReal

theorem min_add_le_min_add_min (r x y : ℝ) (hr : 0 ≤ r) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min r (x+y) ≤ min r x+min r y := by
  rcases le_total r x with h | h
  · rw [min_eq_left h]
    have hh := min_le_left r (x+y)
    have hn : 0 ≤ min r y := le_min hr hy
    linarith only [hh,hn]
  · rw [min_eq_right h]
    rcases le_total r y with h' | h'
    · rw [min_eq_left h']
      have hh := min_le_left r (x+y)
      linarith only [hh,hx]
    · rw [min_eq_right h']
      exact min_le_right _ _

theorem canonical_sqrt_cost_identity (ρ F B : ℝ) (hρ : 0 ≤ ρ) (hF : 0 ≤ F) :
    ((1/sqrt B)*sqrt ρ)*sqrt F = sqrt (ρ*F/B) := by
  rw [sqrt_div (mul_nonneg hρ hF),sqrt_mul hρ]
  ring

theorem certificate_optimal_finite_score {n N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hB : 0 < B) (hN : 0 < N) (C : Certificate N) (hC : Feasible μ ρ B C)
    (S : Finset (Fin n))
    (hopt : ∀ T, finiteSelectionScore ((1/sqrt B)*sqrt ρ)
      (fun i : Fin n => μ.real (ThresholdHC.EntropyTail.band i.val)/((1/2:ℝ)^(i.val+1))^2)
      (fun i => μ.real (ThresholdHC.EntropyTail.band i.val)*min 1 ((1/sqrt B)/((1/2:ℝ)^(i.val+1)))) S ≤
      finiteSelectionScore ((1/sqrt B)*sqrt ρ)
      (fun i : Fin n => μ.real (ThresholdHC.EntropyTail.band i.val)/((1/2:ℝ)^(i.val+1))^2)
      (fun i => μ.real (ThresholdHC.EntropyTail.band i.val)*min 1 ((1/sqrt B)/((1/2:ℝ)^(i.val+1)))) T) :
    min ρ (finiteSelectionScore ((1/sqrt B)*sqrt ρ)
      (fun i : Fin n => μ.real (ThresholdHC.EntropyTail.band i.val)/((1/2:ℝ)^(i.val+1))^2)
      (fun i => μ.real (ThresholdHC.EntropyTail.band i.val)*min 1 ((1/sqrt B)/((1/2:ℝ)^(i.val+1)))) S) ≤
      100000000*(256*C.bias+sqrt ((4294967296*exp 48)*C.variance)) := by
  classical
  let w := fun i : Fin n => μ.real (ThresholdHC.EntropyTail.band i.val)
  let b := fun i : Fin n => (1/2:ℝ)^(i.val+1)
  let F := costEntropy (maskedCost (fun i => w i/(b i)^2) S)
  let O := ∑ i : Fin n, if i ∉ S ∧ 1/sqrt B ≤ b i then w i/(sqrt B*b i) else 0
  let J := ∑ i : Fin n, if i ∉ S ∧ b i < 1/sqrt B then w i else 0
  let R := 256*C.bias+sqrt ((4294967296*exp 48)*C.variance)
  have hR : 0 ≤ R := by dsimp [R]; positivity [hC.bias_nonneg]
  have hw (i) : 0 ≤ w i := measureReal_nonneg
  have hb (i) : 0 < b i := by dsimp [b]; positivity
  have hF : 0 ≤ F := costEntropy_nonneg (maskedCost_nonneg _
    (fun i => div_nonneg (hw i) (sq_nonneg _)) S)
  have hO : 0 ≤ O := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs; exact div_nonneg (hw i) (mul_nonneg (sqrt_nonneg B) (hb i).le); exact le_rfl
  have hJ : 0 ≤ J := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs; exact hw i; exact le_rfl
  have hsplit := ordinary_ignored_penalty_split w b hb (1/sqrt B) S
  have heO : (∑ i : Fin n, if i ∉ S ∧ 1/sqrt B ≤ b i then w i*(1/sqrt B)/b i else 0) = O := by
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [heO] at hsplit
  change (∑ i : Fin n, if i ∈ S then 0 else w i*min 1 ((1/sqrt B)/b i)) = O+J at hsplit
  have hret := certificate_optimal_retained_cost μ ρ B hρ hρ1 hB hN C hC S hopt
  change min ρ (sqrt (ρ*F/B)) ≤ 83886080*R at hret
  have hord := certificate_optimal_ordinary_cost μ ρ B hρ hB hN C hC S hopt
  change O ≤ 2080*R at hord
  have hign := certificate_prefix_ignored_cost μ ρ B hρ.le hB hN C hC S
  change min ρ J ≤ 260*R at hign
  change min ρ (finiteSelectionScore ((1/sqrt B)*sqrt ρ) (fun i => w i/(b i)^2)
    (fun i => w i*min 1 ((1/sqrt B)/b i)) S) ≤ 100000000*R
  unfold finiteSelectionScore
  change min ρ (((1/sqrt B)*sqrt ρ)*sqrt F+
    ∑ i : Fin n, if i ∈ S then 0 else w i*min 1 ((1/sqrt B)/b i)) ≤ 100000000*R
  rw [hsplit,canonical_sqrt_cost_identity ρ F B hρ.le hF]
  have h1 := min_add_le_min_add_min ρ (sqrt (ρ*F/B)) (O+J) hρ.le (sqrt_nonneg _) (add_nonneg hO hJ)
  have h2 := min_add_le_min_add_min ρ O J hρ.le hO hJ
  have h3 := min_le_right ρ O
  nlinarith only [h1,h2,h3,hret,hord,hign,hR]

theorem certificate_finite_canonical_score {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hB : 0 < B) (hN : 0 < N) (C : Certificate N) (hC : Feasible μ ρ B C) (n : ℕ) :
    ∃ S : Finset ℕ, (∀ j ∈ S, j < n) ∧ min ρ (finiteCanonicalScore μ ρ B n S) ≤
      100000000*(256*C.bias+sqrt ((4294967296*exp 48)*C.variance)) := by
  classical
  obtain ⟨S,hopt⟩ := exists_finiteSelection_minimizer ((1/sqrt B)*sqrt ρ)
    (fun i : Fin n => μ.real (ThresholdHC.EntropyTail.band i.val)/((1/2:ℝ)^(i.val+1))^2)
    (fun i => μ.real (ThresholdHC.EntropyTail.band i.val)*min 1 ((1/sqrt B)/((1/2:ℝ)^(i.val+1))))
  let T := S.image Fin.val
  have hmem (i : Fin n) : i.val ∈ T ↔ i ∈ S := by
    constructor
    · intro hi
      obtain ⟨k,hk,hki⟩ := Finset.mem_image.mp hi
      exact (Fin.val_injective hki) ▸ hk
    · exact fun hi => Finset.mem_image.mpr ⟨i,hi,rfl⟩
  refine ⟨T,?_,?_⟩
  · intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact i.isLt
  · have he : finiteCanonicalScore μ ρ B n T = finiteSelectionScore ((1/sqrt B)*sqrt ρ)
        (fun i : Fin n => μ.real (ThresholdHC.EntropyTail.band i.val)/((1/2:ℝ)^(i.val+1))^2)
        (fun i => μ.real (ThresholdHC.EntropyTail.band i.val)*min 1 ((1/sqrt B)/((1/2:ℝ)^(i.val+1)))) S := by
      unfold finiteCanonicalScore finiteSelectionScore maskedCost
      rw [← Fin.sum_univ_eq_sum_range]
      simp_rw [hmem]
    rw [he]
    exact certificate_optimal_finite_score μ ρ B hρ hρ1 hB hN C hC S hopt

theorem certificate_selection_upper {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hB : 0 < B) (hN : 0 < N) (C : Certificate N) (hC : Feasible μ ρ B C) :
    ThresholdHC.EntropyTail.selection μ ρ B ≤
      ENNReal.ofReal (200000000*(256*C.bias+sqrt ((4294967296*exp 48)*C.variance))) := by
  have hh := finite_canonical_uniform_limit μ ρ B
    (100000000*(256*C.bias+sqrt ((4294967296*exp 48)*C.variance))) hρ.le
    (certificate_finite_canonical_score μ ρ B hρ hρ1 hB hN C hC)
  convert hh using 1 <;> congr 1 <;> ring

end ThresholdHC.EntropyTailLower
