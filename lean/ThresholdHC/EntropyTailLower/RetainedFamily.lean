import ThresholdHC.EntropyTailLower.ComparableGroups
import ThresholdHC.EntropyTailLower.TrimmedGroup
import ThresholdHC.EntropyTailLower.JointAllocation
import ThresholdHC.EntropyTailLower.CanonicalGroups

noncomputable section
namespace ThresholdHC.EntropyTailLower
open MeasureTheory Real ThresholdHC.EntropyTailQuantile
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram
open scoped BigOperators ENNReal

theorem certificate_retained_family_bound {I : Type} [Fintype I] [LinearOrder I] [Nonempty I]
    {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B F A : ℝ)
    (hρ : 0 < ρ) (hB : 0 < B) (hF : 0 < F) (hN : 0 < N)
    (C : Certificate N) (hC : Feasible μ ρ B C)
    (j : I → ℕ) (hj : StrictMono j) (hlow : ∀ i, 6 ≤ j i)
    (hw : ∀ i, 0 < μ.real (ThresholdHC.EntropyTail.band (j i)))
    (hA : costTotal (fun i => μ.real (ThresholdHC.EntropyTail.band (j i))/((1/2:ℝ)^(j i+1))^2) ≤ A)
    (hFsum : costEntropy (fun i => μ.real (ThresholdHC.EntropyTail.band (j i))/((1/2:ℝ)^(j i+1))^2) ≤ F)
    (hFcap : F ≤ 4*costEntropy (fun i => μ.real (ThresholdHC.EntropyTail.band (j i))/((1/2:ℝ)^(j i+1))^2))
    (hgap : ∀ i, (sqrt ρ/sqrt F)*(1+log (A/(μ.real (ThresholdHC.EntropyTail.band (j i))/
      ((1/2:ℝ)^(j i+1))^2))) ≤ 2*((1/2:ℝ)^(j i+1))) :
    min ρ (sqrt (ρ*F/B)) ≤
      83886080*(256*C.bias+sqrt ((4294967296*exp 48)*C.variance)) := by
  classical
  let w := fun i => μ.real (ThresholdHC.EntropyTail.band (j i))
  let b := fun i => (1/2:ℝ)^(j i+1)
  let v := fun i => w i/(b i)^2
  change costTotal v ≤ A at hA
  change costEntropy v ≤ F at hFsum
  change F ≤ 4*costEntropy v at hFcap
  let r : I → Fin 2 := fun i => ⟨j i%2,Nat.mod_lt _ (by norm_num)⟩
  let lam := sqrt ρ/sqrt F
  have hb (i) : 0 < b i := by dsimp [b]; positivity
  have hv (i) : 0 < v i := div_pos (hw i) (sq_pos_of_pos (hb i))
  have hlam : 0 < lam := div_pos (sqrt_pos.mpr hρ) (sqrt_pos.mpr hF)
  obtain ⟨T,inst,⟨g⟩⟩ := exists_comparable_ordered_groups v hv r
  letI : Fintype T := inst
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
  have hsumG : (∑ t, G t) ≤ F := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun t _ => (ht t).2.2.2.2.2.2.2.1)
    exact hh.trans (g.entropy_sum_le.trans hFsum)
  have hcapture : F ≤ 5120*∑ t, G t := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun t _ => (ht t).2.2.2.2.2.2.1)
    rw [← Finset.mul_sum] at hh
    have hg := g.capture
    change costEntropy v ≤ 18*∑ t, H t at hg
    have hn := Finset.sum_nonneg (s := Finset.univ) (fun t _ => (hG t).le)
    nlinarith only [hFcap,hg,hh,hn]
  have hL : lam^2 = ρ/F := by
    dsimp [lam]
    rw [div_pow,sq_sqrt hρ.le,sq_sqrt hF.le]
  have hsat (t) : (ρ/F)*(G t)^2 ≤ 4096*(τ t*s t/(a t)^2) := by
    rw [← hL]
    exact (ht t).2.2.2.2.2.2.2.2
  obtain ⟨θ,u,hθ,hθcap,hρsum,hu,hucap,hcost,hfinal⟩ :=
    packed_joint_allocation ρ B F 5120 hρ hB hF (by norm_num) τ s a G hG
      (fun t => (ht t).2.1.le) (fun t => (ht t).2.2.2.1) hGscale hsat hsumG hcapture
  have hbound := certificate_canonical_group_bound μ ρ B hB hN C hC K J hJ hcross hm
    a ha hasmall hmax hsep θ s u hθ (fun t => by rw [hmass]; exact hθcap t) hρsum
    (fun t => by rw [hmass]; exact (ht t).2.2.2.1)
    (fun t k => (ht t).2.2.1 k) hu hucap (fun t => by rw [hmass]; exact hcost t)
  norm_num only [show (16384:ℝ)*5120 = 83886080 by norm_num] at hfinal
  exact hfinal.trans (mul_le_mul_of_nonneg_left hbound (by norm_num))

end ThresholdHC.EntropyTailLower
