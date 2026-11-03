import ThresholdHC.EntropyTailLower.RetainedFamily
import ThresholdHC.EntropyTailLower.GlobalCosts
import ThresholdHC.EntropyTailLower.LargeGapEntropy
import ThresholdHC.EntropyTailLower.RetainedGap

noncomputable section
namespace ThresholdHC.EntropyTailLower
open MeasureTheory Real ThresholdHC.EntropyTailQuantile
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram
open scoped BigOperators

theorem six_index_entropy_bound {I : Type} [Fintype I] (j : I → ℕ)
    (hj : Function.Injective j) (hj6 : ∀ i, j i < 6)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : (∑ i, w i) ≤ 1) :
    costEntropy (fun i => w i/((1/2:ℝ)^(j i+1))^2) ≤ 16384 := by
  have hcard : Fintype.card I ≤ 6 := by
    have h := Fintype.card_le_of_injective (fun i => (⟨j i,hj6 i⟩ : Fin 6))
      (fun _ _ he => hj (congrArg Fin.val he))
    simpa only [Fintype.card_fin] using h
  have hp : (∑ _i : I, (1/6:ℝ)) ≤ 1 := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    have hc : (Fintype.card I:ℝ) ≤ 6 := by exact_mod_cast hcard
    linarith
  let a := fun i => w i/((1/2:ℝ)^(j i+1))^2
  have ha (i) : 0 ≤ a i := div_nonneg (hw i) (sq_nonneg _)
  have he := costEntropy_le_reference ha (fun _i : I => by norm_num : ∀ _i : I, (0:ℝ) < 1/6) hp
  have hl6 : log (6:ℝ) ≤ 3 := by
    have h2 := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    have h3 := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
    have heq : log (6:ℝ) = log 2+log 3 := by
      rw [← log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]; norm_num
    linarith
  have hsnon := Finset.sum_nonneg (s := Finset.univ) (fun i _ => ha i)
  have hmul := mul_le_mul_of_nonneg_right hl6 hsnon
  simp only [one_div,log_inv,sub_neg_eq_add,← Finset.sum_mul] at he
  have ha4096 (i) : a i ≤ 4096*w i := by
    have hbi : (1/64:ℝ) ≤ (1/2:ℝ)^(j i+1) := by
      have h := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) ≤ 1) (show j i+1 ≤ 6 by have := hj6 i; omega)
      norm_num at h
      exact h
    apply (div_le_iff₀ (show (0:ℝ) < ((1/2:ℝ)^(j i+1))^2 by positivity)).mpr
    have hb2 : (1:ℝ) ≤ 4096*((1/2:ℝ)^(j i+1))^2 := by nlinarith only [hbi]
    nlinarith only [mul_le_mul_of_nonneg_left hb2 (hw i)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => ha4096 i)
  rw [← Finset.mul_sum] at hs
  change costEntropy a ≤ 16384
  nlinarith only [he,hmul,hs,hsum]

theorem canonical_high_mask_entropy_bound {n : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (S : Finset (Fin n)) :
    costEntropy (fun i : Fin n => if i.val < 6 then
      maskedCost (fun i => μ.real (ThresholdHC.EntropyTail.band i.val)/
        ((1/2:ℝ)^(i.val+1))^2) S i else 0) ≤ 16384 := by
  classical
  rw [costEntropy_indicator_eq_subtype]
  let I := {i : Fin n // i.val < 6}
  let w : I → ℝ := fun i => if i.val ∈ S then μ.real (ThresholdHC.EntropyTail.band i.val.val) else 0
  have hw (i) : 0 ≤ w i := by dsimp [w]; split_ifs; exact measureReal_nonneg; exact le_rfl
  have hj : Function.Injective (fun i : I => i.val.val) := by
    intro i k he
    exact Subtype.ext (Fin.ext he)
  have hmass : (∑ i, w i) ≤ 1 := by
    apply le_trans _ (canonical_band_mass_sum_le_one μ (fun i : I => i.val.val) hj)
    apply Finset.sum_le_sum
    intro i _
    dsimp [w]
    split_ifs; exact le_rfl; exact measureReal_nonneg
  have hh := six_index_entropy_bound (fun i : I => i.val.val) hj (fun i => i.property) w hw hmass
  convert hh using 1
  congr 1
  funext i
  dsimp [w,maskedCost]
  split_ifs <;> simp

theorem certificate_entropy_cap_65536 {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hB : 0 < B) (C : Certificate N) (hC : Feasible μ ρ B C) (F : ℝ) (hF : F ≤ 65536) :
    min ρ (sqrt (ρ*F/B)) ≤ 256*(256*C.bias+sqrt ((4294967296*exp 48)*C.variance)) := by
  have hroot : sqrt (ρ*F/B) ≤ 256*sqrt (ρ/B) := by
    have hh : ρ*F/B ≤ 65536*(ρ/B) := by
      have h := mul_le_mul_of_nonneg_left hF (div_nonneg hρ.le hB.le)
      convert h using 1 <;> ring
    have hs := sqrt_le_sqrt hh
    rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 65536)] at hs
    norm_num at hs
    exact hs
  have hcap := scaled_min_bound ρ (sqrt (ρ/B)) (sqrt (ρ*F/B)) 256 hρ.le (by norm_num) hroot
  have hl := certificate_label_floor μ ρ B hρ hρ1 hB C hC
  have hb := label_bound_le_annular_bound C hC.variance_nonneg
  nlinarith only [hcap,hl,hb,hC.bias_nonneg]

theorem certificate_optimal_retained_cost {n N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hB : 0 < B) (hN : 0 < N) (C : Certificate N) (hC : Feasible μ ρ B C)
    (S : Finset (Fin n))
    (hopt : ∀ T, finiteSelectionScore ((1/sqrt B)*sqrt ρ)
      (fun i : Fin n => μ.real (ThresholdHC.EntropyTail.band i.val)/((1/2:ℝ)^(i.val+1))^2)
      (fun i => μ.real (ThresholdHC.EntropyTail.band i.val)*min 1 ((1/sqrt B)/((1/2:ℝ)^(i.val+1)))) S ≤
      finiteSelectionScore ((1/sqrt B)*sqrt ρ)
      (fun i : Fin n => μ.real (ThresholdHC.EntropyTail.band i.val)/((1/2:ℝ)^(i.val+1))^2)
      (fun i => μ.real (ThresholdHC.EntropyTail.band i.val)*min 1 ((1/sqrt B)/((1/2:ℝ)^(i.val+1)))) T) :
    min ρ (sqrt (ρ*costEntropy (maskedCost
      (fun i : Fin n => μ.real (ThresholdHC.EntropyTail.band i.val)/((1/2:ℝ)^(i.val+1))^2) S)/B)) ≤
      83886080*(256*C.bias+sqrt ((4294967296*exp 48)*C.variance)) := by
  classical
  let w := fun i : Fin n => μ.real (ThresholdHC.EntropyTail.band i.val)
  let b := fun i : Fin n => (1/2:ℝ)^(i.val+1)
  let a := fun i => w i/(b i)^2
  let X := maskedCost a S
  let F := costEntropy X
  let A := costTotal X
  let R := 256*C.bias+sqrt ((4294967296*exp 48)*C.variance)
  have hR : 0 ≤ R := by dsimp [R]; positivity [hC.bias_nonneg]
  change min ρ (sqrt (ρ*F/B)) ≤ 83886080*R
  by_cases hbounded : F ≤ 65536
  · have hh := certificate_entropy_cap_65536 μ ρ B hρ hρ1 hB C hC F hbounded
    change min ρ (sqrt (ρ*F/B)) ≤ 256*R at hh
    linarith only [hh,hR]
  have hF : 0 < F := by linarith only [hbounded]
  have hw (i) : 0 ≤ w i := measureReal_nonneg
  have hb (i) : 0 < b i := by dsimp [b]; positivity
  have ha (i) : 0 ≤ a i := div_nonneg (hw i) (sq_nonneg _)
  have hX (i) : 0 ≤ X i := maskedCost_nonneg a ha S i
  let p := fun i : Fin n => i ∈ S ∧ ¬i.val < 6 ∧ 0 < w i
  let Y := fun i => if p i then a i else 0
  let G := costEntropy Y
  have heLow : (fun i : Fin n => if i.val < 6 then 0 else X i) = Y := by
    funext i
    by_cases hwpos : 0 < w i
    · by_cases hiS : i ∈ S <;> by_cases hi6 : i.val < 6 <;>
        simp [X,maskedCost,Y,p,hiS,hi6,hwpos]
    · have hz : w i = 0 := le_antisymm (le_of_not_gt hwpos) (hw i)
      by_cases hiS : i ∈ S <;> by_cases hi6 : i.val < 6 <;>
        simp [X,maskedCost,Y,p,a,hiS,hi6,hwpos,hz]
  have hpart := costEntropy_bipartition X hX (fun i => i.val < 6)
  rw [heLow] at hpart
  have hhigh := canonical_high_mask_entropy_bound μ S
  change costEntropy (fun i : Fin n => if i.val < 6 then X i else 0) ≤ 16384 at hhigh
  have hcapture : F ≤ 4*G := by
    change F ≤ 2*costEntropy (fun i : Fin n => if i.val < 6 then X i else 0)+2*G at hpart
    nlinarith only [hpart,hhigh,hbounded]
  have hG : 0 < G := by nlinarith only [hcapture,hF]
  have hY (i) : 0 ≤ Y i := by dsimp [Y]; split_ifs; exact ha i; exact le_rfl
  have hYX (i) : Y i ≤ X i := by
    by_cases hi : p i
    · simp [Y,hi,X,maskedCost,hi.1]
    · simp only [Y,hi,ite_false]
      exact hX i
  have hGF : G ≤ F := costEntropy_mono hY hYX
  have hsome : ∃ i, p i := by
    by_contra hnone
    have hpnone := not_exists.mp hnone
    have hz : G = 0 := by simp [G,Y,hpnone]
    exact (ne_of_gt hG) hz
  obtain ⟨i0,hi0⟩ := hsome
  let I := {i : Fin n // p i}
  letI : Nonempty I := ⟨⟨i0,hi0⟩⟩
  have hGsub : costEntropy (fun i : I => a i) = G :=
    (costEntropy_indicator_eq_subtype p a).symm
  have hAsub : costTotal (fun i : I => a i) ≤ A := by
    change (∑ i : I, a i) ≤ ∑ i, X i
    rw [← sum_indicator_eq_subtype p a]
    exact Finset.sum_le_sum (fun i _ => hYX i)
  have hj : StrictMono (fun i : I => i.val.val) := fun _ _ h => h
  have hgap (i : I) : (sqrt ρ/sqrt F)*(1+log (A/(a i))) ≤ 2*b i := by
    have hg := optimal_retained_band_gap w b hw hb ρ (1/sqrt B) hρ.le
      (by positivity) S hopt i.val i.property.1 i.property.2.2
    change sqrt ρ*(1+log (A/a i)) ≤ 2*b i*sqrt F at hg
    have he : (sqrt ρ/sqrt F)*(1+log (A/a i)) =
        (sqrt ρ*(1+log (A/a i)))/sqrt F := by ring
    rw [he]
    exact (div_le_iff₀ (sqrt_pos.mpr hF)).mpr hg
  apply certificate_retained_family_bound μ ρ B F A hρ hB hF hN C hC
    (fun i : I => i.val.val) hj
  · intro i
    have hh := i.property.2.1
    omega
  · exact fun i => i.property.2.2
  · exact hAsub
  · rw [hGsub]
    exact hGF
  · rw [hGsub]
    exact hcapture
  · exact hgap

end ThresholdHC.EntropyTailLower
