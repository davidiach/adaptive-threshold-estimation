import LargeBudgetFresh
import ThresholdHC.HardBudget.Application

/-! One fresh flip or a second flip of a previously observed coin at gap 1/5. -/
noncomputable section
namespace ThresholdHC.SharpRMS.Revisit
open Tier3 Tier5 Proofs

def headProb (p : ℝ) := (3+4*p)/10

/-- Probability of heads, conditional on the previous observation of this coin. -/
def nextHead (p : ℝ) : Option Bool → ℝ
  | none => headProb p
  | some true => ((9+40*p)/100)/headProb p
  | some false => (21/100)/(1-headProb p)

abbrev law {n : ℕ} (pol : List Bool → Option ℕ) (p : ℝ) (w : Prefix n) :=
  creationLaw pol (fun _ => 1/5) (fun _ => p) w

private theorem conditional (p : ℝ) (hp : p∈Set.Icc 0 1) (b : Option Bool) (o : Option Bool) :
    let like := fun a => b.elim 1 (fun x => obsProb a (some x))
    p*like (1/2+1/5)*obsProb (1/2+1/5) o+(1-p)*like (1/2-1/5)*obsProb (1/2-1/5) o =
      (p*like (1/2+1/5)+(1-p)*like (1/2-1/5))*obsProb (nextHead p b) o := by
  have pos : 0<headProb p := by unfold headProb; linarith [hp.1]
  have lt : headProb p<1 := by unfold headProb; linarith [hp.2]
  have nh : headProb p≠0 := pos.ne'
  have nt : 1-headProb p≠0 := (sub_pos.mpr lt).ne'
  have aux (z : Option Bool) : (p*(z.elim 1 fun x => obsProb (1/2+1/5) (some x))+
      (1-p)*(z.elim 1 fun x => obsProb (1/2-1/5) (some x))) =
      z.elim 1 (fun x => obsProb (headProb p) (some x)) := by
    cases z with
    | none => simp
    | some x => cases x <;> simp [obsProb,headProb] <;> ring
  dsimp only
  rw [aux]
  cases b with
  | none => cases o with
    | none => simp [obsProb]
    | some y => cases y <;> simp [obsProb,nextHead,headProb] <;> ring
  | some x =>
    cases o with
    | none => simp [obsProb]
    | some y => cases x <;> cases y <;> simp [obsProb,nextHead] <;> field_simp [nh,nt] <;> (try unfold headProb) <;> ring

/-- Previous queries of label i consist exactly of the indicated one or none. -/
theorem step {n : ℕ} (pol : List Bool → Option ℕ) (p : ℝ) (hp : p∈Set.Icc 0 1) (w : Prefix n)
    (i : ℕ) (act : pol (fullHist w)=some i) (old : Option (Fin n))
    (history : ∀ j : Fin n, pol (histBefore w j)=some i ↔ old=some j)
    (o : Option Bool) :
    law pol p (Fin.snoc w o) = law pol p w * obsProb (nextHead p (old.bind w)) o := by
  let m := coinCap (n+1) pol
  have hi : i < m := selected_lt_coinCap pol (Fin.snoc w o) (Fin.last n) i (by simpa only [histBefore_snoc_last] using act)
  let a : Fin m := ⟨i,hi⟩
  let π := capPolicy m pol
  have active : π (fullHist w)=some a := by simp [π,capPolicy,act,hi,a]
  have hist (j : Fin n) : π (histBefore w j)=some a ↔ old=some j := by
    rw [←history]
    cases e : pol (histBefore w j) with
    | none => simp [π,capPolicy,e]
    | some v => by_cases hv : v < m <;> simp [π,capPolicy,e,hv,a,Fin.ext_iff]
                omega
  have likes (q : ℝ) : coinLike π w a q = old.elim 1 (fun j => obsProb q (w j)) := by
    unfold coinLike
    simp_rw [hist]
    cases old with
    | none => simp
    | some j => simp [Finset.prod_ite_eq]
  unfold law
  rw [creationLaw_eq_capped pol _ _ w m (coinCap_le_succ n pol)]
  change transcriptLaw π _ _ (Fin.snoc w o) = transcriptLaw π _ _ w * _
  rw [transcriptLaw_query π _ _ w a active,transcriptLaw_split π _ _ w a]
  unfold coinMix
  simp only [likes,mul_assoc]
  congr 1
  cases old with
  | none => simpa [mul_assoc] using conditional p hp none o
  | some j =>
    cases e : w j with
    | none => simp [e,obsProb]
    | some b => simpa [e,mul_assoc] using conditional p hp (some b) o

theorem valid_word (label : List Bool → ℕ) {n : ℕ} (hn : n≤25) (p : ℝ) (hp : p∈Set.Icc 0 1)
    (w : Prefix n) (nz : law (HardBudget.stopAt 25 label) p w≠0) : ∃ u : Fin n → Bool, w=fun i => some (u i) := by
  let pol := HardBudget.stopAt 25 label
  induction n with
  | zero => exact ⟨fun i => i.elim0,Subsingleton.elim ..⟩
  | succ n ih =>
    rw [←Fin.snoc_init_self w] at nz ⊢
    generalize Fin.init w = v at nz ⊢
    generalize w (Fin.last n) = o at nz ⊢
    have prev : law pol p v≠0 := by
      intro e
      have pos (a) : 0≤law pol p (Fin.snoc v a) := (creationLaw_total _ pol _ _ (fun _ => by norm_num) (fun _ => hp)).1 _
      have z := creationLaw_sum_extensions pol (fun _ => 1/5) (fun _ => p) v
      exact nz (le_antisymm ((Finset.single_le_sum (fun a _ => pos a) (Finset.mem_univ o)).trans (z.trans e).le) (pos o))
    obtain ⟨u,rfl⟩ := ih (by omega) v prev
    have len : (fullHist (fun i => some (u i))).length=n := by
      unfold fullHist
      rw [show (fun i => some (u i))=some ∘ u from rfl,←List.map_ofFn]
      simp
    have act : pol (fullHist (fun i => some (u i)))=some (label (fullHist (fun i => some (u i)))) := by
      simp [pol,HardBudget.stopAt,len,show n<25 by omega]
    cases o with
    | none =>
      apply False.elim (nz ?_)
      let m := coinCap (n+1) pol
      have lt := selected_lt_coinCap pol (Fin.snoc (fun i => some (u i)) none) (Fin.last n) _
        (by simpa only [histBefore_snoc_last] using act)
      exact transcriptLaw_query_none (capPolicy m pol) _ _ _ ⟨_,lt⟩ (by simp [capPolicy,act,lt,m])
    | some b =>
      refine ⟨Fin.snoc u b,?_⟩
      funext i
      exact Fin.lastCases (by simp) (fun j => by simp) i

end ThresholdHC.SharpRMS.Revisit
