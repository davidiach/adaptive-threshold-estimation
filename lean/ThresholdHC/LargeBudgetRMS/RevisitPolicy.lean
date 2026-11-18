import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Fin
import ThresholdHC.LargeBudgetRMS.LargeBudgetFresh

/-! Twenty fresh observations followed by five distinct revisits or five fresh coins. -/
noncomputable section
namespace ThresholdHC.SharpRMS.Revisit
open Tier3 Tier5 Proofs

def mode (j : ℕ) : Option Bool :=
  if 5≤j ∧ j≤9 then some true else if 11≤j ∧ j≤15 then some false else none

def targets (v : List Bool) : Finset (Fin 20) :=
  match mode (v.count true) with
  | none => ∅
  | some b => Finset.univ.filter (fun i => v[i.val]?.getD false=b)

/-- Use eligible pilot indices in increasing order. New labels start at twenty. -/
def follow (v : List Bool) (k : ℕ) : ℕ :=
  if h : k<(targets v).card then ((targets v).orderEmbOfFin rfl ⟨k,h⟩).val else 20+k

def label (xs : List Bool) : ℕ :=
  if xs.length<20 then xs.length else follow (xs.take 20) (xs.length-20)

theorem follow_inj (v : List Bool) : Function.Injective (follow v) := by
  intro k l eq
  unfold follow at eq
  split at eq <;> split at eq
  · exact congrArg Fin.val (((targets v).orderEmbOfFin rfl).injective (Fin.ext eq))
  · have h := ((targets v).orderEmbOfFin rfl ⟨k,by assumption⟩).isLt
    omega
  · have h := ((targets v).orderEmbOfFin rfl ⟨l,by assumption⟩).isLt
    omega
  · omega

private theorem counts (v : List Bool) : v.count false+v.count true=v.length := by
  induction v with
  | nil => simp
  | cons x xs ih => cases x <;> simp <;> omega

theorem follow_mode (v : List Bool) (len : v.length=20) (k : ℕ) (hk : k<5) :
    (mode (v.count true)=none ∧ follow v k=20+k) ∨
    (∃ b, mode (v.count true)=some b ∧ follow v k<20 ∧ v[follow v k]?=some b) := by
  cases h : mode (v.count true) with
  | none => exact Or.inl ⟨rfl,by simp [follow,targets,h]⟩
  | some b =>
    have count : (targets v).card=v.count b := by
      let w : List.Vector Bool 20 := ⟨v,len⟩
      change _ = w.toList.count b
      convert Fin.card_filter_univ_eq_vector_get_eq_count b w using 2
      simp only [targets,h]
      apply Finset.filter_congr
      intro i _
      have hi : i.val<v.length := by rw [len]; exact i.isLt
      simp [List.getElem?_eq_getElem hi,w,List.Vector.get]
    have eligible : 5≤v.count b := by
      have total := counts v
      unfold mode at h
      split at h
      · cases h; omega
      split at h
      · cases h; omega
      contradiction
    have hl : k<(targets v).card := by omega
    let i := (targets v).orderEmbOfFin rfl ⟨k,hl⟩
    have mem : i∈targets v := Finset.orderEmbOfFin_mem ..
    have hi : i.val<v.length := by rw [len]; exact i.isLt
    have val : v[i.val]?=some b := by
      simp only [targets,h,Finset.mem_filter,Finset.mem_univ,true_and] at mem
      simpa only [List.getElem?_eq_getElem hi,Option.getD_some,Option.some.injEq] using mem
    exact Or.inr ⟨b,rfl,by simpa only [follow,dite_eq_left hl] using i.isLt,by simpa only [follow,dite_eq_left hl] using val⟩

theorem full_bits {n : ℕ} (u : Fin n → Bool) : fullHist (fun i => some (u i))=List.ofFn u := by
  unfold fullHist
  rw [show (fun i => some (u i))=some ∘ u from rfl,←List.map_ofFn]
  simp

theorem hist_bits {n : ℕ} (u : Fin n → Bool) (j : Fin n) :
    histBefore (fun i => some (u i)) j=(List.ofFn u).take j.val := by
  change fullHist (fun k : Fin j.val => some (u (Fin.castLE j.isLt.le k))) = _
  rw [full_bits]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

end ThresholdHC.SharpRMS.Revisit
