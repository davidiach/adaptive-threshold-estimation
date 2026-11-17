import ThresholdHC.SharpRMS.Attainment
import ThresholdHC.Tier5.PriorRatio
import ThresholdHC.Tier3.Examples

/-! Naming a fresh coin by its birth history or its birth index gives the same
observable law. The argument also covers impossible transcripts. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open Tier3 Tier5 Proofs

def fourPolicy (name : List Bool → ℕ) (xs : List Bool) : Option ℕ :=
  if xs.length < 4 then some (name xs) else none

private def atom (n : ℕ) (p : ℝ) (o : Option Bool) : ℝ :=
  if n<4 then obsProb p o else if o=none then 1 else 0

private def freshMass (p : ℝ) : {n : ℕ} → Prefix n → ℝ
  | 0, _ => 1
  | n+1, w => freshMass p (Fin.init w)*atom n p (w (Fin.last n))

private theorem mass_shape (p : ℝ) {n : ℕ} (w : Prefix n) (hn : freshMass p w ≠ 0) :
    (fullHist w).length=min n 4 := by
  induction n with
  | zero => simp [fullHist]
  | succ n ih =>
    rw [←Fin.snoc_init_self w] at hn ⊢
    generalize Fin.init w = v at hn ⊢
    generalize w (Fin.last n) = o at hn ⊢
    simp only [freshMass,Fin.init_snoc,Fin.snoc_last] at hn
    have h := ih v (left_ne_zero_of_mul hn)
    have ho := right_ne_zero_of_mul hn
    rw [fullHist_snoc_example,List.length_append,h]
    by_cases hd : n<4 <;> cases o <;> simp_all [atom,obsProb] <;> omega

private theorem next_zero {n : ℕ} (pol : List Bool → Option ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (w : Prefix n) (o : Option Bool) (hz : creationLaw pol (fun _ => 1/2) (fun _ => p) w=0) :
    creationLaw pol (fun _ => 1/2) (fun _ => p) (Fin.snoc w o)=0 := by
  let P := fun a => creationLaw pol (fun _ => 1/2) (fun _ => p) (Fin.snoc w a)
  have pos (a) : 0 ≤ P a := (creationLaw_total _ pol _ _ (fun _ => by norm_num) (fun _ => hp)).1 _
  have sum := creationLaw_sum_extensions pol (fun _ => 1/2) (fun _ => p) w
  rw [hz] at sum
  exact le_antisymm ((Finset.single_le_sum (f:=P) (fun a _ => pos a) (Finset.mem_univ o)).trans_eq sum) (pos o)

private theorem query_fresh {n : ℕ} (pol : List Bool → Option ℕ) (p : ℝ) (w : Prefix n)
    (i : ℕ) (hi : pol (fullHist w)=some i)
    (unused : ∀ j : Fin n, pol (histBefore w j) ≠ some i) (o : Option Bool) :
    creationLaw pol (fun _ => 1/2) (fun _ => p) (Fin.snoc w o) =
      creationLaw pol (fun _ => 1/2) (fun _ => p) w * obsProb p o := by
  let m := coinCap (n+1) pol
  have lt : i < m := selected_lt_coinCap pol (Fin.snoc w o) (Fin.last n) i (by simpa only [histBefore_snoc_last] using hi)
  let a : Fin m := ⟨i,lt⟩
  let π := capPolicy m pol
  have act : π (fullHist w)=some a := by simp [π,capPolicy,hi,lt,a]
  have fresh : a ∉ queriedCoins π w := by
    simp only [queriedCoins,Finset.mem_biUnion,Finset.mem_univ,true_and,not_exists]
    intro j
    cases h : pol (histBefore w j) with
    | none => simp [π,capPolicy,h]
    | some k =>
      have diff : k ≠ i := by intro e; exact unused j (h.trans (congrArg some e))
      by_cases hk : k < m <;> simp [π,capPolicy,h,hk,a,Ne.symm diff]
  have c := coinLike_eq_one_of_not_queried π w a fresh
  rw [creationLaw_eq_capped pol _ _ w m (coinCap_le_succ n pol)]
  change transcriptLaw π _ _ (Fin.snoc w o) = transcriptLaw π _ _ w * _
  rw [transcriptLaw_query π _ _ w a act,transcriptLaw_split π _ _ w a]
  simp only [coinMix,c,mul_one]
  cases o with
  | none => simp [obsProb]
  | some b => cases b <;> simp [obsProb] <;> ring

private theorem stop_word {n : ℕ} (pol : List Bool → Option ℕ) (p : ℝ) (w : Prefix n)
    (hs : pol (fullHist w)=none) (o : Option Bool) :
    creationLaw pol (fun _ => 1/2) (fun _ => p) (Fin.snoc w o) =
      if o=none then creationLaw pol (fun _ => 1/2) (fun _ => p) w else 0 := by
  rw [creationLaw_eq_capped pol _ _ w _ (coinCap_le_succ n pol)]
  exact transcriptLaw_stop _ _ _ w (by simp [capPolicy,hs]) o

private theorem named_mass (name : List Bool → ℕ) (lengths : ∀ x y, name x=name y → x.length=y.length)
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) {n : ℕ} (w : Prefix n) :
    creationLaw (fourPolicy name) (fun _ => 1/2) (fun _ => p) w = freshMass p w := by
  induction n with
  | zero => simp [creationLaw,transcriptLaw_factor,pathValidity,coinLike,freshMass]
  | succ n ih =>
    rw [←Fin.snoc_init_self w]
    generalize Fin.init w = v
    generalize w (Fin.last n) = o
    simp only [freshMass,Fin.init_snoc,Fin.snoc_last]
    by_cases zero : freshMass p v=0
    · rw [zero,zero_mul]
      exact next_zero _ p hp v o ((ih v).trans zero)
    have shape := mass_shape p v zero
    by_cases h : n<4
    · have len : (fullHist v).length=n := shape.trans (min_eq_left h.le)
      have active : (fullHist v).length<4 := len.trans_lt h
      rw [query_fresh _ p v (name (fullHist v)) (by simp [fourPolicy,active]) _ o,ih]
      · simp [atom,h]
      intro j
      have lj := histBefore_length_le v j
      have lt : (histBefore v j).length<4 := lt_trans (lj.trans_lt j.isLt) h
      intro eq
      have same := lengths _ _ (show name (histBefore v j)=name (fullHist v) by simpa [fourPolicy,lt] using eq)
      omega
    · have len : (fullHist v).length=4 := shape.trans (min_eq_right (by omega))
      rw [stop_word _ p v (by simp [fourPolicy,len]) o,ih]
      cases o <;> simp [atom,h]

theorem fresh_labels_word {n : ℕ} (w : Prefix n) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    creationLaw (fourPolicy Encodable.encode) (fun _ => 1/2) (fun _ => p) w =
      creationLaw (freshPolicy 3) (fun _ => 1/2) (fun _ => p) w := by
  apply (named_mass Encodable.encode (fun x y e => congrArg List.length (Encodable.encode_injective e)) p hp w).trans
  exact (named_mass List.length (fun _ _ e => e) p hp w).symm

end ThresholdHC.SharpRMS
