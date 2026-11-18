import OrderedExperiment
import Mathlib.Tactic

namespace PilotFeedback.Ordered
noncomputable section
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.SharpRMS.Revisit

/-- Stage (pilot or suffix), coin choice, and answer. A multiset of these
triples records precisely the pilot count and the counts in each suffix group. -/
abbrev Symbol := Bool × Option Bool × Bool
abbrev Counts := Multiset Symbol

def counts (A : Schedule) : List Bool → List Bool → Counts
  | _, [] => 0
  | xs, b::bs => (decide (xs.length<18),action A xs,b) ::ₘ counts A (xs++[b]) bs

def likelihood (p : ℝ) (s : Counts) : ℝ :=
  (s.map (fun x => if x.2.2 then nextHead p x.2.1 else 1-nextHead p x.2.1)).prod

private theorem sum_words {n : ℕ} (f : (Fin (n+1) → Bool) → ℝ) :
    ∑ s, f s = (∑ t, f (Fin.cons false t)) + ∑ t, f (Fin.cons true t) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp,Fintype.sum_prod_type,Fintype.sum_bool]
  exact add_comm ..

theorem expand_run (A : Schedule) (p : ℝ) (X : List Bool → ℝ) (n : ℕ) (xs : List Bool) :
    run A p X n xs = ∑ w : Fin n → Bool, likelihood p (counts A xs (List.ofFn w)) *
      X (xs++List.ofFn w) := by
  induction n generalizing xs with
  | zero => simp [run,counts,likelihood]
  | succ n ih =>
    rw [run,ih,ih,sum_words,Finset.mul_sum,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro w _ <;>
      simp [counts,likelihood,List.append_assoc,mul_assoc]

abbrev Word := Fin 25 → Bool
def statistic (A : Schedule) (w : Word) := counts A [] (List.ofFn w)
def support (A : Schedule) := Finset.univ.image (statistic A)
def fibre (A : Schedule) (s : Counts) := Finset.univ.filter (fun w => statistic A w = s)

/-- The conditional resampling rule: average any observable over the ordered
words having the given counts, with equal weights. It has no parameter p. -/
def uniformOrder (A : Schedule) (s : Counts) (X : List Bool → ℝ) : ℝ :=
  (∑ w ∈ fibre A s, X (List.ofFn w)) / (fibre A s).card

def groupedMass (A : Schedule) (p : ℝ) (s : Counts) := (fibre A s).card * likelihood p s

private theorem fibre_pos (A : Schedule) {s : Counts} (hs : s ∈ support A) :
    0 < (fibre A s).card := by
  obtain ⟨w,_,hw⟩ := Finset.mem_image.mp hs
  exact Finset.card_pos.mpr ⟨w,by simp [fibre,hw]⟩

theorem uniformOrder_one (A : Schedule) {s : Counts} (hs : s ∈ support A) :
    uniformOrder A s (fun _ => 1) = 1 := by
  simp [uniformOrder,(fibre_pos A hs).ne']

/-- Exact reconstruction against every test of the full ordered transcript.
In particular indicator tests give the entire output law at every p. -/
theorem ordered_reduction (A : Schedule) (p : ℝ) (hp : p ∈ Set.Icc 0 1) (X : List Bool → ℝ) :
    (∑ w : Prefix 25, law (policy A) p w * X (fullHist w)) =
      ∑ s ∈ support A, groupedMass A p s * uniformOrder A s X := by
  classical
  rw [ordered_expect A p hp,expand_run]
  simp only [List.nil_append]
  change (∑ w : Word, likelihood p (statistic A w) * X (List.ofFn w)) = _
  rw [←Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := support A)
    (g := statistic A) (fun w hw => Finset.mem_image_of_mem _ hw)]
  apply Finset.sum_congr rfl
  intro s hs
  have pos := fibre_pos A hs
  have same : (∑ w ∈ fibre A s, likelihood p (statistic A w) * X (List.ofFn w)) =
      likelihood p s * ∑ w ∈ fibre A s, X (List.ofFn w) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [(Finset.mem_filter.mp hu).2]
  change (∑ w ∈ fibre A s, _) = _
  rw [same]
  unfold groupedMass uniformOrder
  field_simp [Nat.cast_ne_zero.mpr pos.ne']

/-- The coefficient multiplying the resampling kernel is the actual marginal
probability of the observed counts in the original ordered experiment. -/
theorem counts_marginal (A : Schedule) (p : ℝ) (hp : p ∈ Set.Icc 0 1) {s : Counts}
    (hs : s ∈ support A) :
    (∑ w : Prefix 25, law (policy A) p w *
      (if counts A [] (fullHist w) = s then (1:ℝ) else 0)) = groupedMass A p s := by
  classical
  rw [ordered_reduction A p hp (fun xs => if counts A [] xs = s then 1 else 0)]
  have row (t : Counts) (ht : t ∈ support A) :
      uniformOrder A t (fun xs => if counts A [] xs = s then 1 else 0) =
        if t=s then 1 else 0 := by
    unfold uniformOrder
    have eq := Finset.sum_congr (s₁ := fibre A t) rfl (fun w hw =>
      congrArg (fun q => if q=s then (1:ℝ) else 0) ((Finset.mem_filter.mp hw).2 : statistic A w=t))
    change (∑ w ∈ fibre A t, if statistic A w=s then (1:ℝ) else 0) / _ = _
    rw [eq]
    by_cases e : t=s
    · subst t
      simp [(Finset.card_pos.mp (fibre_pos A hs)).ne_empty]
    · simp [e]
  calc
    _ = ∑ t ∈ support A, groupedMass A p t * (if t=s then 1 else 0) :=
      Finset.sum_congr rfl (fun t ht => congrArg _ (row t ht))
    _ = _ := by simp [Finset.sum_ite_eq',hs]

end
end PilotFeedback.Ordered
