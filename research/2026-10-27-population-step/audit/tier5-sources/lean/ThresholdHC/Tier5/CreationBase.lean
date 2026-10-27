import ThresholdHC.Tier5.Model
import ThresholdHC.Tier5.CreationPadding

noncomputable section
namespace ThresholdHC.Tier5
open MeasureTheory ThresholdHC.Proofs ThresholdHC.Tier3

local instance optionNatSpace : MeasurableSpace (Option ℕ) := ⊤
local instance optionFinSpace (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤

def creationPolicyCode {Seed : Type} (n : ℕ)
    (pol : Seed → List Bool → Option ℕ) (u : Seed) :
    (Prefix n × Fin n) → Option ℕ := fun wt => pol u (histBefore wt.1 wt.2)

theorem measurable_creationPolicyCode {Seed : Type} [MeasurableSpace Seed]
    (n : ℕ) (pol : Seed → List Bool → Option ℕ)
    (hp : ∀ xs, Measurable (fun u => pol u xs)) :
    Measurable (creationPolicyCode n pol) := by
  apply Measurable.of_eval
  intro wt
  exact hp (histBefore wt.1 wt.2)

theorem measurable_coinCap {Seed : Type} [MeasurableSpace Seed]
    (n : ℕ) (pol : Seed → List Bool → Option ℕ)
    (hp : ∀ xs, Measurable (fun u => pol u xs)) :
    Measurable (fun u => coinCap n (pol u)) := by
  exact (measurable_of_countable
    (fun c : (Prefix n × Fin n) → Option ℕ =>
      Finset.univ.sup (fun wt => (c wt).getD 0) + 1)).comp
    (measurable_creationPolicyCode n pol hp)

theorem measurable_capPolicy {Seed : Type} [MeasurableSpace Seed]
    (m : ℕ) (pol : Seed → List Bool → Option ℕ)
    (hp : ∀ xs, Measurable (fun u => pol u xs)) (xs : List Bool) :
    Measurable (fun u => capPolicy m (pol u) xs) := by
  exact (measurable_of_countable (fun o : Option ℕ =>
    o.bind (fun i => if hi : i < m then some (⟨i, hi⟩ : Fin m) else none))).comp (hp xs)

theorem selected_lt_coinCap {n : ℕ} (pol : List Bool → Option ℕ)
    (w : Prefix n) (t : Fin n) (i : ℕ) (hi : pol (histBefore w t) = some i) :
    i < coinCap n pol := by
  have h := Finset.le_sup (s := Finset.univ)
    (f := fun wt : Prefix n × Fin n => (pol (histBefore wt.1 wt.2)).getD 0)
    (Finset.mem_univ (w,t))
  simpa [coinCap, hi] using Nat.lt_succ_of_le h

theorem coinCap_le_succ (n : ℕ) (pol : List Bool → Option ℕ) :
    coinCap n pol ≤ coinCap (n+1) pol := by
  unfold coinCap
  apply Nat.add_le_add_right
  apply Finset.sup_le
  intro wt hwt
  have h := Finset.le_sup (s := Finset.univ)
    (f := fun vt : Prefix (n+1) × Fin (n+1) =>
      (pol (histBefore vt.1 vt.2)).getD 0)
    (Finset.mem_univ (Fin.snoc wt.1 none, wt.2.castSucc))
  simpa only [histBefore_snoc_castSucc] using h

theorem coinCap_mono (pol : List Bool → Option ℕ) : Monotone (fun n => coinCap n pol) :=
  monotone_nat_of_le_succ (fun n => coinCap_le_succ n pol)

theorem capPolicy_succ_agree {m n : ℕ} (pol : List Bool → Option ℕ)
    (w : Prefix n) (hm : coinCap n pol ≤ m) (t : Fin n) :
    capPolicy (m+1) pol (histBefore w t) =
      (capPolicy m pol (histBefore w t)).map Fin.castSucc := by
  cases he : pol (histBefore w t) with
  | none => simp [capPolicy, he]
  | some i =>
    have hi : i < m := (selected_lt_coinCap pol w t i he).trans_le hm
    simp [capPolicy, he, hi, hi.le]

theorem cappedLaw_succ_eq {n m : ℕ} (pol : List Bool → Option ℕ)
    (d q : ℕ → ℝ) (w : Prefix n) (hm : coinCap n pol ≤ m) :
    transcriptLaw (capPolicy (m+1) pol) (fun i => d i.val) (fun i => q i.val) w =
      transcriptLaw (capPolicy m pol) (fun i => d i.val) (fun i => q i.val) w := by
  exact transcriptLaw_unused_last (capPolicy m pol) (capPolicy (m+1) pol)
    (fun i => d i.val) (fun i => q i.val) w (capPolicy_succ_agree pol w hm)

theorem creationLaw_eq_capped {n : ℕ} (pol : List Bool → Option ℕ)
    (d q : ℕ → ℝ) (w : Prefix n) (m : ℕ) (hm : coinCap n pol ≤ m) :
    creationLaw pol d q w =
      transcriptLaw (capPolicy m pol) (fun i => d i.val) (fun i => q i.val) w := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih => rw [cappedLaw_succ_eq pol d q w hm]; exact ih

theorem creationLaw_sum_extensions {n : ℕ} (pol : List Bool → Option ℕ)
    (d q : ℕ → ℝ) (w : Prefix n) :
    (∑ o : Option Bool, creationLaw pol d q (Fin.snoc w o)) = creationLaw pol d q w := by
  unfold creationLaw
  rw [transcriptLaw_sum_extensions]
  exact (creationLaw_eq_capped pol d q w (coinCap (n+1) pol) (coinCap_le_succ n pol)).symm

theorem creationLaw_total (n : ℕ) (pol : List Bool → Option ℕ)
    (d q : ℕ → ℝ) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    (∀ w : Prefix n, 0 ≤ creationLaw pol d q w) ∧
      ∑ w : Prefix n, creationLaw pol d q w = 1 :=
  transcript_law_total (coinCap n pol) n (capPolicy (coinCap n pol) pol)
    (fun i => d i.val) (fun i => q i.val) (fun i => hd i.val) (fun i => hq i.val)

theorem creation_law_total : CreationTotalStatement := creationLaw_total

theorem creation_law_consistent : CreationConsistencyStatement := by
  intro n pol d q w _ _
  exact creationLaw_sum_extensions pol d q w

end ThresholdHC.Tier5
