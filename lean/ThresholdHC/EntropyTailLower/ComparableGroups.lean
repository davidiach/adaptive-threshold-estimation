import ThresholdHC.EntropyTailLower.EntropyTiers
import ThresholdHC.EntropyTailLower.SeparatedGroups

noncomputable section
namespace ThresholdHC.EntropyTailLower
open Real ThresholdHC.EntropyTailQuantile
open scoped BigOperators

theorem costTotal_comp_injective_le {I J : Type} [Fintype I] [Fintype J]
    (a : J → ℝ) (ha : ∀ j, 0 ≤ a j) (e : I → J) (he : Function.Injective e) :
    costTotal (fun i => a (e i)) ≤ costTotal a := by
  classical
  exact Finset.sum_le_sum_of_injOn e he.injOn (Finset.subset_univ _)
    (fun _ _ => le_rfl) (fun j _ _ => ha j)

theorem costTotal_orderEmb_eq_indicator {I : Type} [Fintype I] [LinearOrder I]
    (S : Finset I) (a : I → ℝ) :
    costTotal (fun i => a (S.orderEmbOfFin rfl i)) =
      costTotal (fun i => if i ∈ S then a i else 0) := by
  letI : Fintype S := Subtype.fintype (fun i : I => i ∈ S)
  have h := Fintype.sum_equiv (S.orderIsoOfFin rfl).toEquiv
    (fun i => a (S.orderEmbOfFin rfl i)) (fun i : S => a i) (fun _ => rfl)
  exact h.trans (sum_indicator_eq_subtype (fun i => i ∈ S) a).symm

theorem costEntropy_orderEmb_eq_indicator {I : Type} [Fintype I] [LinearOrder I]
    (S : Finset I) (a : I → ℝ) :
    costEntropy (fun i => a (S.orderEmbOfFin rfl i)) =
      costEntropy (fun i => if i ∈ S then a i else 0) := by
  letI : Fintype S := Subtype.fintype (fun i : I => i ∈ S)
  have h := costEntropy_equiv (S.orderIsoOfFin rfl).toEquiv (fun i : S => a i)
  exact h.trans (costEntropy_indicator_eq_subtype (fun i => i ∈ S) a).symm

theorem entropy_tier_parity_refinement {I : Type} [Fintype I]
    (a : I → ℝ) (ha : ∀ i, 0 ≤ a i) (K : ℕ)
    (p : I → Fin K) (r : I → Fin 2)
    (h : costEntropy a ≤ 9*∑ k, costEntropy (fun i => if p i = k then a i else 0)) :
    costEntropy a ≤ 18*∑ q : Fin K × Fin 2,
      costEntropy (fun i => if (p i,r i) = q then a i else 0) := by
  classical
  have hsplit (k : Fin K) : costEntropy (fun i => if p i = k then a i else 0) ≤
      2*∑ v : Fin 2, costEntropy (fun i => if (p i,r i) = (k,v) then a i else 0) := by
    have hn (i) : 0 ≤ if p i = k then a i else 0 := by
      split_ifs; exact ha i; exact le_rfl
    have hh := costEntropy_bipartition (fun i => if p i = k then a i else 0) hn
      (fun i => r i = 0)
    have he0 : (fun i => if r i = 0 then (if p i = k then a i else 0) else 0) =
        (fun i => if (p i,r i) = (k,0) then a i else 0) := by
      funext i
      by_cases hp : p i = k <;> by_cases hr : r i = 0 <;> simp [hp,hr]
    have he1 : (fun i => if r i = 0 then 0 else (if p i = k then a i else 0)) =
        (fun i => if (p i,r i) = (k,1) then a i else 0) := by
      funext i
      have hr : r i = 0 ∨ r i = 1 := by omega
      rcases hr with hr | hr <;> by_cases hp : p i = k <;> simp [hp,hr]
    rw [he0,he1] at hh
    simpa only [Fin.sum_univ_two,mul_add] using hh
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hsplit k)
  rw [← Finset.mul_sum] at hs
  have he : (∑ q : Fin K × Fin 2, costEntropy (fun i => if (p i,r i) = q then a i else 0)) =
      ∑ k, ∑ v : Fin 2, costEntropy (fun i => if (p i,r i) = (k,v) then a i else 0) := by
    exact Fintype.sum_prod_type _
  rw [he]
  linarith only [h,hs]

theorem costEntropy_partition_sum_le {I Q : Type} [Fintype I] [Fintype Q]
    [DecidableEq Q]
    (a : I → ℝ) (ha : ∀ i, 0 ≤ a i) (p : I → Q) :
    (∑ q, costEntropy (fun i => if p i = q then a i else 0)) ≤ costEntropy a := by
  classical
  have hn (q : Q) (i : I) : 0 ≤ if p i = q then a i else 0 := by
    split_ifs; exact ha i; exact le_rfl
  have h := costEntropy_sum_superadditive (fun q i => if p i = q then a i else 0) hn
  simpa using h

structure ComparableOrderedGroups {I : Type} [Fintype I] [LinearOrder I]
    (a : I → ℝ) (r : I → Fin 2) (T : Type) [Fintype T] where
  size : T → ℕ
  index : (t : T) → Fin (size t) → I
  size_pos : ∀ t, 0 < size t
  increasing : ∀ t, StrictMono (index t)
  parity : ∀ t i j, r (index t i) = r (index t j)
  disjoint : ∀ t u, t ≠ u → ∀ i j, index t i ≠ index u j
  scale : T → ℝ
  scale_pos : ∀ t, 0 < scale t
  lower : ∀ t i, scale t ≤ a (index t i)
  upper : ∀ t i, a (index t i) ≤ 4*scale t
  capture : costEntropy a ≤ 18*∑ t, costEntropy (fun i => a (index t i))
  entropy_sum_le : (∑ t, costEntropy (fun i => a (index t i))) ≤ costEntropy a

theorem exists_comparable_ordered_groups {I : Type} [Fintype I] [LinearOrder I] [Nonempty I]
    (a : I → ℝ) (ha : ∀ i, 0 < a i) (r : I → Fin 2) :
    ∃ (T : Type) (_ : Fintype T), Nonempty (ComparableOrderedGroups a r T) := by
  classical
  obtain ⟨K,p,c,hc,hbounds,hcapture⟩ := exists_entropy_tier_partition a ha
  let Q := Fin K × Fin 2
  let f : I → Q := fun i => (p i,r i)
  let S : Q → Finset I := fun q => Finset.univ.filter (fun i => f i = q)
  let T := {q : Q // (S q).Nonempty}
  let size : T → ℕ := fun t => (S t.val).card
  let index : (t : T) → Fin (size t) → I := fun t => (S t.val).orderEmbOfFin rfl
  have hj (t : T) (i : Fin (size t)) : f (index t i) = t.val := by
    have hmem := (S t.val).orderEmbOfFin_mem rfl i
    exact (Finset.mem_filter.mp hmem).2
  have hentropy (t : T) : costEntropy (fun i => a (index t i)) =
      costEntropy (fun i => if f i = t.val then a i else 0) := by
    rw [show (fun i => a (index t i)) = (fun i => a ((S t.val).orderEmbOfFin rfl i)) from rfl]
    rw [costEntropy_orderEmb_eq_indicator]
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
  have hzero (q : Q) (hq : ¬(S q).Nonempty) :
      costEntropy (fun i => if f i = q then a i else 0) = 0 := by
    have hne (i : I) : f i ≠ q := by
      intro he
      exact hq ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,he⟩⟩
    simp only [hne,ite_false,costEntropy_zero]
  have hsum : (∑ t : T, costEntropy (fun i => if f i = t.val then a i else 0)) =
      ∑ q : Q, costEntropy (fun i => if f i = q then a i else 0) := by
    rw [← sum_indicator_eq_subtype (fun q : Q => (S q).Nonempty)
      (fun q : Q => costEntropy (fun i => if f i = q then a i else 0))]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : (S q).Nonempty
    · simp only [hq,ite_true]
    · simp only [hq,ite_false,hzero q hq]
  have hfullsum : (∑ t, costEntropy (fun i => a (index t i))) =
      ∑ q : Q, costEntropy (fun i => if f i = q then a i else 0) := by
    simp_rw [hentropy]
    exact hsum
  refine ⟨T,inferInstance,⟨{
    size := size
    index := index
    size_pos := fun t => Finset.card_pos.mpr t.property
    increasing := fun t => (S t.val).orderEmbOfFin rfl |>.strictMono
    parity := ?_
    disjoint := ?_
    scale := fun t => c t.val.1
    scale_pos := fun t => hc _
    lower := ?_
    upper := ?_
    capture := ?_
    entropy_sum_le := ?_
  }⟩⟩
  · intro t i j
    exact (congrArg Prod.snd (hj t i)).trans (congrArg Prod.snd (hj t j)).symm
  · intro t u htu i j he
    apply htu
    apply Subtype.ext
    exact (hj t i).symm.trans ((congrArg f he).trans (hj u j))
  · intro t i
    have hh := (hbounds (index t i)).1.le
    have he := congrArg Prod.fst (hj t i)
    change p (index t i) = t.val.1 at he
    rwa [he] at hh
  · intro t i
    have hh := (hbounds (index t i)).2
    have he := congrArg Prod.fst (hj t i)
    change p (index t i) = t.val.1 at he
    rwa [he] at hh
  · rw [hfullsum]
    exact entropy_tier_parity_refinement a (fun i => (ha i).le) K p r hcapture
  · rw [hfullsum]
    exact costEntropy_partition_sum_le a (fun i => (ha i).le) f

end ThresholdHC.EntropyTailLower
