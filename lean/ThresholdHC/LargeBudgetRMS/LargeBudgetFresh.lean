import ThresholdHC.SharpRMS.Attainment
import ThresholdHC.Tier5.PriorRatio

/-! Exact binomial recursion for a fixed number of fresh flips at a single gap. -/
noncomputable section
namespace ThresholdHC.SharpRMS.LargeBudget
open Tier3 Tier5 Proofs

private theorem next_zero {n : ℕ} (pol : List Bool → Option ℕ) (d p : ℝ) (hd : d ∈ Set.Icc 0 (1/2)) (hp : p ∈ Set.Icc 0 1)
    (w : Prefix n) (o : Option Bool) (hz : creationLaw pol (fun _ => d) (fun _ => p) w=0) :
    creationLaw pol (fun _ => d) (fun _ => p) (Fin.snoc w o)=0 := by
  let P := fun a => creationLaw pol (fun _ => d) (fun _ => p) (Fin.snoc w a)
  have pos (a) : 0 ≤ P a := (creationLaw_total _ pol _ _ (fun _ => hd) (fun _ => hp)).1 _
  have sum := creationLaw_sum_extensions pol (fun _ => d) (fun _ => p) w
  rw [hz] at sum
  exact le_antisymm ((Finset.single_le_sum (f:=P) (fun a _ => pos a) (Finset.mem_univ o)).trans_eq sum) (pos o)

private theorem query_fresh {n : ℕ} (pol : List Bool → Option ℕ) (d p : ℝ) (w : Prefix n)
    (i : ℕ) (hi : pol (fullHist w)=some i)
    (unused : ∀ j : Fin n, pol (histBefore w j) ≠ some i) (o : Option Bool) :
    creationLaw pol (fun _ => d) (fun _ => p) (Fin.snoc w o) =
      creationLaw pol (fun _ => d) (fun _ => p) w * obsProb (1/2+(2*p-1)*d) o := by
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


private theorem mass_step {N n : ℕ} (hn : n<N+1) (d p : ℝ) (hd : d∈Set.Icc 0 (1/2))
    (hp : p∈Set.Icc 0 1) (v : Prefix n) (o : Option Bool) :
    creationLaw (freshPolicy N) (fun _ => d) (fun _ => p) (Fin.snoc v o) =
    creationLaw (freshPolicy N) (fun _ => d) (fun _ => p) v * obsProb (1/2+(2*p-1)*d) o := by
  let P := fun {k : ℕ} (w : Prefix k) => creationLaw (freshPolicy N) (fun _ => d) (fun _ => p) w
  have shape (k : ℕ) (hk : k≤N+1) (w : Prefix k) (hz : P w≠0) : (fullHist w).length=k := by
    induction k with
    | zero => simp [fullHist]
    | succ k ih =>
      rw [←Fin.snoc_init_self w] at hz ⊢
      generalize Fin.init w = v at hz ⊢
      generalize w (Fin.last k) = a at hz ⊢
      have prev : P v≠0 := fun h => hz (next_zero _ d p hd hp v a h)
      have len := ih (by omega) v prev
      have act : freshPolicy N (fullHist v)=some k := by simp [freshPolicy,len,show k<N+1 by omega]
      have unused (j : Fin k) : freshPolicy N (histBefore v j)≠some k := by
        have lt := (histBefore_length_le v j).trans_lt j.isLt
        simp [freshPolicy,show (histBefore v j).length<N+1 by omega,lt.ne]
      cases a with
      | some b => simp [fullHist_snoc_example,len]
      | none => exact False.elim (hz (by rw [show P (Fin.snoc v (none : Option Bool))=_
          from query_fresh _ d p v k act unused none]; simp [obsProb]))
  by_cases hz : P v=0
  · change P (Fin.snoc v o)=P v*_
    rw [hz,zero_mul]
    exact next_zero _ d p hd hp v o hz
  have len := shape n hn.le v hz
  apply query_fresh _ d p v n (by simp [freshPolicy,len,hn])
  intro j
  have lt := (histBefore_length_le v j).trans_lt j.isLt
  simp [freshPolicy,show (histBefore v j).length<N+1 by omega,lt.ne]

def headsNat {n : ℕ} (w : Prefix n) : ℕ := ∑ i, if w i=some true then 1 else 0

def binomialAverage (p : ℝ) (f : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, k => f k
  | n+1, k => (1-p)*binomialAverage p f n k + p*binomialAverage p f n (k+1)

theorem fresh_average (N n : ℕ) (hn : n≤N+1) (d p : ℝ) (hd : d∈Set.Icc 0 (1/2))
    (hp : p∈Set.Icc 0 1) (f : ℕ → ℝ) (k : ℕ) :
    (∑ w : Prefix n, creationLaw (freshPolicy N) (fun _ => d) (fun _ => p) w*f (k+headsNat w)) =
      binomialAverage (1/2+(2*p-1)*d) f n k := by
  induction n generalizing k with
  | zero => simp [creationLaw,transcriptLaw_factor,pathValidity,coinLike,headsNat,binomialAverage]
  | succ n ih =>
    let b := 1/2+(2*p-1)*d
    rw [sum_snoc]
    have step (v : Prefix n) (o : Option Bool) : headsNat (Fin.snoc v o)=headsNat v+(if o=some true then 1 else 0) := by
      unfold headsNat
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc,Fin.snoc_last]
    simp_rw [mass_step (by omega : n<N+1) d p hd hp,step]
    simp only [Fintype.sum_option,Fintype.sum_bool,obsProb,Bool.false_eq_true,↓reduceIte,
      Option.some.injEq,reduceCtorEq,mul_zero,zero_mul,zero_add,add_zero]
    have id (v : Prefix n) :
        creationLaw (freshPolicy N) (fun _=>d) (fun _=>p) v*b*f (k+(headsNat v+1)) +
        creationLaw (freshPolicy N) (fun _=>d) (fun _=>p) v*(1-b)*f (k+headsNat v) =
        (1-b)*(creationLaw (freshPolicy N) (fun _=>d) (fun _=>p) v*f (k+headsNat v)) +
        b*(creationLaw (freshPolicy N) (fun _=>d) (fun _=>p) v*f ((k+1)+headsNat v)) := by
      rw [show k+(headsNat v+1)=k+1+headsNat v by omega]; ring
    dsimp only [b] at id
    simp_rw [id]
    rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,ih (by omega),ih (by omega)]
    rfl

end ThresholdHC.SharpRMS.LargeBudget
