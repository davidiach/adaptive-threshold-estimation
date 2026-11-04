import ThresholdHC.EntropyTailSharp.Groups
import ThresholdHC.FiniteQuantile.Core

/-! Apply the sharper annular variance price to the filtered dyadic core. Each group uses the full-rarity allocation of the finite-law development. -/
noncomputable section
open MeasureTheory Set Real
open scoped BigOperators ENNReal
namespace ThresholdHC.EntropyTailSharp
open ThresholdHC.FiniteQuantile ThresholdHC.EntropyTailLower ThresholdHC.EntropyTailQuantile
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.RareAboveTwo

theorem filtered_core_certificate_bound_sharp {I : Type} [Fintype I] [LinearOrder I] [Nonempty I]
    {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B F A : ℝ)
    (hρ : 0 < ρ) (hB : 0 < B) (hF : 0 < F) (hN : 0 < N)
    (C : Certificate N) (hC : Feasible μ ρ B C)
    (j : I → ℕ) (hj : StrictMono j) (hlow : ∀ i, 6 ≤ j i)
    (hw : ∀ i, 0 < μ.real (ThresholdHC.EntropyTail.band (j i)))
    (hA : costTotal (fun i => μ.real (ThresholdHC.EntropyTail.band (j i))/((1/2:ℝ)^(j i+1))^2) ≤ A)
    (hFcap : F ≤ 16*costEntropy (fun i => μ.real (ThresholdHC.EntropyTail.band (j i))/((1/2:ℝ)^(j i+1))^2))
    (hgap : ∀ i, (65536*(sqrt ρ/sqrt F))*(1+log (A/(μ.real (ThresholdHC.EntropyTail.band (j i))/
      ((1/2:ℝ)^(j i+1))^2))) ≤ 2*((1/2:ℝ)^(j i+1))) :
    min ρ (sqrt (ρ*F/B)) ≤
      256*(256*C.bias+sqrt ((16384*exp 48)*C.variance)) := by
  classical
  let w := fun i => μ.real (ThresholdHC.EntropyTail.band (j i))
  let b := fun i => (1/2:ℝ)^(j i+1)
  let v := fun i => w i/(b i)^2
  change costTotal v ≤ A at hA
  change F ≤ 16*costEntropy v at hFcap
  let r : I → Fin 2 := fun i => ⟨j i%2,Nat.mod_lt _ (by norm_num)⟩
  let lam := 65536*(sqrt ρ/sqrt F)
  have hb (i) : 0 < b i := by dsimp [b]; positivity
  have hv (i) : 0 < v i := div_pos (hw i) (sq_pos_of_pos (hb i))
  have hlam : 0 < lam := mul_pos (by norm_num) (div_pos (sqrt_pos.mpr hρ) (sqrt_pos.mpr hF))
  obtain ⟨T,inst,⟨g⟩⟩ := exists_comparable_ordered_groups v hv r
  let : Fintype T := inst
  let K := fun t => g.size t-Nat.clog 4 (g.size t)
  let e : (t : T) → Fin (K t) → Fin (g.size t) := fun t => Fin.castLE (Nat.sub_le _ _)
  let J : (t : T) → Fin (K t) → ℕ := fun t k => j (g.index t (e t k))
  let a := fun t => b (g.index t ⟨0,g.size_pos t⟩)
  let s := fun t => g.scale t*((g.size t:ℝ)*(lam*(1+log (g.size t:ℝ))/16))^2
  let τ := fun t => ∑ k, w (g.index t (e t k))
  let G := fun t => costEntropy (fun k => v (g.index t (e t k)))
  let H := fun t => costEntropy (fun k => v (g.index t k))
  have hfullsep (t : T) (k l : Fin (g.size t)) (hkl : l.val = k.val+1) :
      4*b (g.index t l) ≤ b (g.index t k) := by
    apply canonical_parity_separation (fun k => j (g.index t k)) (hj.comp (g.increasing t))
    · intro k l
      exact congrArg Fin.val (g.parity t k l)
    · exact hkl
  have ht (t : T) : 0 < K t ∧ 0 < s t ∧
      (∀ k, s t ≤ w (g.index t (e t k))) ∧ s t ≤ τ t ∧
      (∀ k, b (g.index t (e t k)) ≤ a t) ∧ τ t/(a t)^2 ≤ G t ∧
      H t ≤ 64*G t ∧ G t ≤ H t ∧
      lam^2*(G t)^2 ≤ 4096*(τ t*s t/(a t)^2) := by
    apply comparable_retained_group_trim (g.size t) (g.size_pos t)
      (fun k => w (g.index t k)) (fun k => b (g.index t k)) (g.scale t) A lam
      (g.scale_pos t) hlam (fun k => hb _) (g.lower t) (g.upper t)
    · exact (costTotal_comp_injective_le v (fun i => (hv i).le) (g.index t)
        (g.increasing t).injective).trans hA
    · exact fun k => hgap (g.index t k)
    · exact hfullsep t
  have hJ (t) : Function.Injective (J t) := hj.injective.comp
    ((g.increasing t).injective.comp (Fin.castLE_injective (Nat.sub_le _ _)))
  have hcross (t u : T) (htu : t ≠ u) (k : Fin (K t)) (l : Fin (K u)) : J t k ≠ J u l := by
    intro he
    exact g.disjoint t u htu _ _ (hj.injective he)
  have hmass (t) : μ.real (canonicalGroup (J t)) = τ t := canonicalGroup_mass μ (J t) (hJ t)
  have hτ (t) : 0 < τ t := (ht t).2.1.trans_le (ht t).2.2.2.1
  have hm (t) : μ (canonicalGroup (J t)) ≠ 0 := by
    intro hz
    have hzreal : μ.real (canonicalGroup (J t)) = 0 := by simp [measureReal_def,hz]
    have hp := hτ t
    rw [← hmass t,hzreal] at hp
    exact (lt_irrefl _ hp)
  have ha (t) : 0 < a t := hb _
  have hasmall (t) : a t ≤ 1/128 := by
    have hh := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) ≤ 1) (show 7 ≤ j (g.index t ⟨0,g.size_pos t⟩)+1 by
        have := hlow (g.index t ⟨0,g.size_pos t⟩); omega)
    norm_num at hh
    exact hh
  have hmax (t k) : (1/2:ℝ)^(J t k+1) ≤ a t := (ht t).2.2.2.2.1 k
  have hsep (t) (k l : Fin (K t)) (hkl : l.val = k.val+1) :
      4*((1/2:ℝ)^(J t l+1)) ≤ (1/2:ℝ)^(J t k+1) := hfullsep t (e t k) (e t l) hkl
  have hGscale (t) : τ t/(a t)^2 ≤ G t := (ht t).2.2.2.2.2.1
  have hG (t) : 0 < G t := (div_pos (hτ t) (sq_pos_of_pos (ha t))).trans_le (hGscale t)
  have hcapture : F ≤ 65536*∑ t, G t := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun t _ => (ht t).2.2.2.2.2.2.1)
    rw [← Finset.mul_sum] at hh
    have hg := g.capture
    change costEntropy v ≤ 18*∑ t, H t at hg
    have hn := Finset.sum_nonneg (s := Finset.univ) (fun t _ => (hG t).le)
    nlinarith only [hFcap,hg,hh,hn]
  have hL : lam^2 = (65536:ℝ)^2*(ρ/F) := by
    dsimp [lam]
    rw [mul_pow,div_pow,sq_sqrt hρ.le,sq_sqrt hF.le]
  have hsat (t) : (65536:ℝ)^2*(ρ/F)*(G t)^2 ≤ 4096*(τ t*s t/(a t)^2) := by
    rw [← hL]
    exact (ht t).2.2.2.2.2.2.2.2
  obtain ⟨θ,u,hθ,hθcap,hρsum,hu,hucap,hcost,hfinal⟩ :=
    full_rarity_allocation G τ s a hρ hB hF hG
      (fun t => (ht t).2.1.le) (fun t => (ht t).2.2.2.1) hGscale hcapture hsat
  have hbound := certificate_canonical_group_bound_sharp μ ρ B hB hN C hC K J hJ hcross hm
    a ha hasmall hmax hsep θ s u hθ (fun t => by rw [hmass]; exact hθcap t) hρsum.le
    (fun t => by rw [hmass]; exact (ht t).2.2.2.1)
    (fun t k => (ht t).2.2.1 k) hu hucap (fun t => by rw [hmass]; exact hcost t)
  exact hfinal.trans (mul_le_mul_of_nonneg_left hbound (by norm_num))

theorem filtered_prefix_certificate_sharp {n N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B t : ℝ} (hρ : 0 < ρ) (hB : 0 < B) (ht : 0 < t)
    (hbefore : ∀ j < n, t ≤ bandEdge j) (hN : 0 < N)
    (C : Certificate N) (hC : Feasible μ ρ B C)
    (hlarge : 262144 < prefixCoreEntropy μ n)
    (hcut : 32*(65536*(sqrt ρ/sqrt (prefixCoreEntropy μ n))) ≤ t) :
    min ρ (sqrt (ρ*prefixCoreEntropy μ n/B)) ≤
      256*(256*C.bias + sqrt ((16384*exp 48)*C.variance)) := by
  classical
  let w := fun i : Fin n => μ.real (EntropyTail.band i.val)
  let b := fun i : Fin n => bandEdge i.val
  let a := fun i => w i/(b i)^2
  let F := costEntropy a
  let A := costTotal a
  let lam := 65536*(sqrt ρ/sqrt F)
  have hw (i) : 0 ≤ w i := measureReal_nonneg
  have hb (i) : 0 < b i := bandEdge_pos _
  have ha (i) : 0 ≤ a i := div_nonneg (hw i) (sq_nonneg _)
  change 262144 < F at hlarge
  have hF : 0 < F := by linarith only [hlarge]
  let bad := fun i : Fin n => discardedBand (a i) (b i) A lam
  let S := Finset.univ.filter (fun i => ¬bad i)
  let X := maskedCost a S
  have hX := maskedCost_nonneg a ha S
  have hbad := discarded_entropy a ha ht (lam := lam)
    (by dsimp [lam]; positivity) hcut hbefore
  change costEntropy (fun i => if bad i then a i else 0) ≤ A/8 at hbad
  have hx : (fun i => if bad i then 0 else a i) = X := by
    funext i
    by_cases h : bad i <;> simp [X, maskedCost, S, h]
  have hfirst := costEntropy_bipartition a ha bad
  rw [hx] at hfirst
  have hAF : A ≤ F := costTotal_le_costEntropy ha
  have hkeep : F ≤ F/4 + 2*costEntropy X := by linarith only [hfirst,hbad,hAF]
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
        simp [X,maskedCost,Y,p,a,hiS,hi6,hz]
  have hpart := costEntropy_bipartition X hX (fun i => i.val < 6)
  rw [heLow] at hpart
  have hhigh := canonical_high_mask_entropy_bound μ S
  simp only [one_div] at hhigh
  change costEntropy (fun i : Fin n => if i.val < 6 then X i else 0) ≤ 16384 at hhigh
  have hcapture : F ≤ 16*G := by
    change costEntropy X ≤ 2*costEntropy (fun i : Fin n => if i.val < 6 then X i else 0)+2*G at hpart
    nlinarith only [hkeep,hpart,hhigh,hlarge]
  have hG : 0 < G := by nlinarith only [hcapture,hF]
  have hsome : ∃ i, p i := by
    by_contra hnone
    have hpnone := not_exists.mp hnone
    have hz : G = 0 := by simp [G,Y,hpnone]
    exact (ne_of_gt hG) hz
  obtain ⟨i0,hi0⟩ := hsome
  let I := {i : Fin n // p i}
  let : Nonempty I := ⟨⟨i0,hi0⟩⟩
  have hGsub : costEntropy (fun i : I => a i) = G :=
    (costEntropy_indicator_eq_subtype p a).symm
  have hAsub : costTotal (fun i : I => a i) ≤ A :=
    costTotal_comp_injective_le a ha Subtype.val Subtype.val_injective
  have hj : StrictMono (fun i : I => i.val.val) := fun _ _ h => h
  have hgap (i : I) : lam*(1+log (A/a i.val)) ≤ 2*b i.val := by
    have hnot := (Finset.mem_filter.mp i.property.1).2
    exact le_of_not_gt (fun h => hnot ⟨div_pos i.property.2.2 (sq_pos_of_pos (hb _)), h⟩)
  have hpack := filtered_core_certificate_bound_sharp μ ρ B F A hρ hB hF hN C hC
    (fun i : I => i.val.val) hj
  simp only [one_div] at hpack
  apply hpack
  · intro i
    have hh := i.property.2.1
    omega
  · exact fun i => i.property.2.2
  · exact hAsub
  · change F ≤ 16*costEntropy (fun i : I => a i.val)
    rw [hGsub]
    exact hcapture
  · exact hgap

end ThresholdHC.EntropyTailSharp
