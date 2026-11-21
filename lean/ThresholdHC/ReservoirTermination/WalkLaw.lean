import ThresholdHC.ReservoirTermination.FirstPassage
import ThresholdHC.Tier5.CreationBase
import ThresholdHC.Tier5.PriorRatio

/-!
The exact finite-prefix law of the walk policy in the Tier 5 creation model.

While the walk is alive the policy queries the label equal to the number of
observations so far, which no earlier step queried, so each observation is a fresh
coin and has parameter `1/2 + (2q-1)d`. After the walk reaches one every entry is
empty. Hence the expectation of a function of the observed history is `walkExp`.
The helpers `walk_next_zero`, `walk_query_fresh` and `walk_stop_word` are copies of
private lemmas of `LargeBudgetRMS/LargeBudgetFresh.lean` and `SharpRMS/FreshLabels.lean`
(the last generalized from the gap one half to every gap).
-/

noncomputable section
namespace ThresholdHC.ReservoirTermination
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Proofs

theorem walk_fullHist_snoc {n : ℕ} (w : Fin n → Option Bool) (o : Option Bool) :
    fullHist (Fin.snoc w o) = fullHist w ++ o.toList := by
  unfold fullHist
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  cases o <;> simp [List.concat_eq_append]

private theorem walk_next_zero {n : ℕ} (pol : List Bool → Option ℕ) (d p : ℝ)
    (hd : 0 ≤ d ∧ d ≤ 1/2) (hp : 0 ≤ p ∧ p ≤ 1)
    (w : Prefix n) (o : Option Bool) (hz : creationLaw pol (fun _ => d) (fun _ => p) w = 0) :
    creationLaw pol (fun _ => d) (fun _ => p) (Fin.snoc w o) = 0 := by
  let P := fun a => creationLaw pol (fun _ => d) (fun _ => p) (Fin.snoc w a)
  have pos (a) : 0 ≤ P a := (creationLaw_total _ pol _ _ (fun _ => hd) (fun _ => hp)).1 _
  have sum := creationLaw_sum_extensions pol (fun _ => d) (fun _ => p) w
  rw [hz] at sum
  exact le_antisymm ((Finset.single_le_sum (f := P) (fun a _ => pos a)
    (Finset.mem_univ o)).trans_eq sum) (pos o)

private theorem walk_query_fresh {n : ℕ} (pol : List Bool → Option ℕ) (d p : ℝ) (w : Prefix n)
    (i : ℕ) (hi : pol (fullHist w) = some i)
    (unused : ∀ j : Fin n, pol (histBefore w j) ≠ some i) (o : Option Bool) :
    creationLaw pol (fun _ => d) (fun _ => p) (Fin.snoc w o) =
      creationLaw pol (fun _ => d) (fun _ => p) w * obsProb (1/2+(2*p-1)*d) o := by
  let m := coinCap (n+1) pol
  have lt : i < m := selected_lt_coinCap pol (Fin.snoc w o) (Fin.last n) i
    (by simpa only [histBefore_snoc_last] using hi)
  let a : Fin m := ⟨i, lt⟩
  let π := capPolicy m pol
  have act : π (fullHist w) = some a := by simp [π, capPolicy, hi, lt, a]
  have fresh : a ∉ queriedCoins π w := by
    simp only [queriedCoins, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists]
    intro j
    cases h : pol (histBefore w j) with
    | none => simp [π, capPolicy, h]
    | some k =>
      have diff : k ≠ i := by intro e; exact unused j (h.trans (congrArg some e))
      by_cases hk : k < m <;> simp [π, capPolicy, h, hk, a, Ne.symm diff]
  have c := coinLike_eq_one_of_not_queried π w a fresh
  rw [creationLaw_eq_capped pol _ _ w m (coinCap_le_succ n pol)]
  change transcriptLaw π _ _ (Fin.snoc w o) = transcriptLaw π _ _ w * _
  rw [transcriptLaw_query π _ _ w a act, transcriptLaw_split π _ _ w a]
  simp only [coinMix, c, mul_one]
  cases o with
  | none => simp [obsProb]
  | some b => cases b <;> simp [obsProb] <;> ring

private theorem walk_stop_word {n : ℕ} (pol : List Bool → Option ℕ) (d p : ℝ) (w : Prefix n)
    (hs : pol (fullHist w) = none) (o : Option Bool) :
    creationLaw pol (fun _ => d) (fun _ => p) (Fin.snoc w o) =
      if o = none then creationLaw pol (fun _ => d) (fun _ => p) w else 0 := by
  rw [creationLaw_eq_capped pol _ _ w _ (coinCap_le_succ n pol)]
  exact transcriptLaw_stop _ _ _ w (by simp [capPolicy, hs]) o

/-- One step of the walk law: absorbed once the walk equals one, a fresh observation
otherwise. -/
theorem walk_step_of_shape {n : ℕ} (d q : ℝ) (hd : 0 ≤ d ∧ d ≤ 1/2) (hq : 0 ≤ q ∧ q ≤ 1)
    (hshape : ∀ v : Prefix n, creationLaw walkPolicy (fun _ => d) (fun _ => q) v ≠ 0 →
      walkValue (fullHist v) ≠ 1 → (fullHist v).length = n)
    (v : Prefix n) (o : Option Bool) :
    creationLaw walkPolicy (fun _ => d) (fun _ => q) (Fin.snoc v o) =
      creationLaw walkPolicy (fun _ => d) (fun _ => q) v *
        (if walkValue (fullHist v) = 1 then (if o = none then 1 else 0)
          else obsProb (1/2+(2*q-1)*d) o) := by
  by_cases hz : creationLaw walkPolicy (fun _ => d) (fun _ => q) v = 0
  · rw [hz, zero_mul]
    exact walk_next_zero walkPolicy d q hd hq v o hz
  by_cases hs : walkValue (fullHist v) = 1
  · rw [walk_stop_word walkPolicy d q v (by simp [walkPolicy, hs]) o]
    simp only [hs, ↓reduceIte]
    split_ifs <;> ring
  · have len := hshape v hz hs
    have unused (j : Fin n) : walkPolicy (histBefore v j) ≠ some n := by
      have lt := (histBefore_length_le v j).trans_lt j.isLt
      unfold walkPolicy
      split_ifs
      · simp
      · simp only [ne_eq, Option.some.injEq]
        omega
    rw [walk_query_fresh walkPolicy d q v n (by simp [walkPolicy, hs, len]) unused o]
    simp only [hs, ↓reduceIte]

/-- While the walk is alive every earlier step observed a coin. -/
theorem walk_shape (d q : ℝ) (hd : 0 ≤ d ∧ d ≤ 1/2) (hq : 0 ≤ q ∧ q ≤ 1) :
    ∀ (n : ℕ) (v : Prefix n), creationLaw walkPolicy (fun _ => d) (fun _ => q) v ≠ 0 →
      walkValue (fullHist v) ≠ 1 → (fullHist v).length = n := by
  intro n
  induction n with
  | zero => intro v _ _; simp [fullHist]
  | succ n ih =>
    intro v hz hs
    rw [← Fin.snoc_init_self v] at hz hs ⊢
    generalize Fin.init v = u at hz hs ⊢
    generalize v (Fin.last n) = a at hz hs ⊢
    rw [walk_step_of_shape d q hd hq ih u a] at hz
    have hu : creationLaw walkPolicy (fun _ => d) (fun _ => q) u ≠ 0 := left_ne_zero_of_mul hz
    have ha := right_ne_zero_of_mul hz
    by_cases hstop : walkValue (fullHist u) = 1
    · simp only [hstop, ↓reduceIte] at ha
      have : a = none := by by_contra h; simp [h] at ha
      subst this
      rw [walk_fullHist_snoc] at hs
      simp [hstop] at hs
    · simp only [hstop, ↓reduceIte] at ha
      cases a with
      | none => simp [obsProb] at ha
      | some b =>
        rw [walk_fullHist_snoc, List.length_append, ih u hu hstop]
        simp

theorem walk_step {n : ℕ} (d q : ℝ) (hd : 0 ≤ d ∧ d ≤ 1/2) (hq : 0 ≤ q ∧ q ≤ 1)
    (v : Prefix n) (o : Option Bool) :
    creationLaw walkPolicy (fun _ => d) (fun _ => q) (Fin.snoc v o) =
      creationLaw walkPolicy (fun _ => d) (fun _ => q) v *
        (if walkValue (fullHist v) = 1 then (if o = none then 1 else 0)
          else obsProb (1/2+(2*q-1)*d) o) :=
  walk_step_of_shape d q hd hq (walk_shape d q hd hq n) v o

/-- Expectations of functions of the observed history are `walkExp`. -/
theorem walk_sum_eq (d q : ℝ) (hd : 0 ≤ d ∧ d ≤ 1/2) (hq : 0 ≤ q ∧ q ≤ 1) :
    ∀ (n : ℕ) (g : List Bool → ℝ),
      ∑ w : Prefix n, creationLaw walkPolicy (fun _ => d) (fun _ => q) w * g (fullHist w) =
        walkExp (1/2+(2*q-1)*d) n g := by
  intro n
  induction n with
  | zero =>
    intro g
    have htot := (creationLaw_total 0 walkPolicy (fun _ => d) (fun _ => q)
      (fun _ => hd) (fun _ => hq)).2
    rw [Fintype.sum_unique] at htot ⊢
    rw [htot, one_mul, walkExp_zero]
    simp [fullHist]
  | succ n ih =>
    intro g
    rw [sum_snoc]
    have inner (v : Prefix n) :
        ∑ o : Option Bool, creationLaw walkPolicy (fun _ => d) (fun _ => q) (Fin.snoc v o) *
          g (fullHist (Fin.snoc v o)) =
        creationLaw walkPolicy (fun _ => d) (fun _ => q) v *
          walkOp (1/2+(2*q-1)*d) g (fullHist v) := by
      simp_rw [walk_step d q hd hq v, walk_fullHist_snoc]
      unfold walkOp
      by_cases h : walkValue (fullHist v) = 1
      · simp [h]
      · simp [h, Fintype.sum_option, obsProb]
        ring
    simp_rw [inner]
    rw [ih, walkExp_succ]

theorem workOf_eq_length : ∀ {n : ℕ} (w : Prefix n), workOf w = ((fullHist w).length : ℝ)
  | 0, w => by simp [workOf, fullHist]
  | n+1, w => by
    rw [← Fin.snoc_init_self w]
    generalize Fin.init w = v
    generalize w (Fin.last n) = o
    rw [workOf_snoc, walk_fullHist_snoc, List.length_append, workOf_eq_length v]
    cases o <;> simp

theorem finiteHistory_last {n : ℕ} (w : Prefix n) :
    finiteHistory w (Fin.last n) = fullHist w := rfl

theorem finiteHistory_snoc_castSucc {n : ℕ} (v : Prefix n) (o : Option Bool)
    (k : Fin (n+1)) :
    finiteHistory (Fin.snoc v o : Prefix (n+1)) k.castSucc = finiteHistory v k := by
  unfold finiteHistory
  congr 2
  funext j
  change @Fin.snoc n (fun _ => Option Bool) v o
    (Fin.castSucc (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)) = _
  exact Fin.snoc_castSucc _ _ _

/-- On the support, a stop at any earlier time persists to the end. -/
theorem walk_absorb (d q : ℝ) (hd : 0 ≤ d ∧ d ≤ 1/2) (hq : 0 ≤ q ∧ q ≤ 1) :
    ∀ (n : ℕ) (w : Prefix n), creationLaw walkPolicy (fun _ => d) (fun _ => q) w ≠ 0 →
      ∀ k : Fin (n+1), walkPolicy (finiteHistory w k) = none →
        walkPolicy (fullHist w) = none := by
  intro n
  induction n with
  | zero =>
    intro w _ k hk
    have hk0 : k = Fin.last 0 := by
      ext
      have := k.isLt
      simp only [Fin.val_last]
      omega
    rwa [hk0, finiteHistory_last] at hk
  | succ n ih =>
    intro w hz k hk
    induction k using Fin.lastCases with
    | last => rwa [finiteHistory_last] at hk
    | cast j =>
      rw [← Fin.snoc_init_self w] at hz hk ⊢
      generalize Fin.init w = u at hz hk ⊢
      generalize w (Fin.last n) = a at hz hk ⊢
      rw [finiteHistory_snoc_castSucc] at hk
      rw [walk_step d q hd hq u a] at hz
      have hu := left_ne_zero_of_mul hz
      have ha := right_ne_zero_of_mul hz
      have hstop := ih u hu j hk
      have hv : walkValue (fullHist u) = 1 := by
        unfold walkPolicy at hstop
        split_ifs at hstop with h
        exact h
      simp only [hv, ↓reduceIte] at ha
      have : a = none := by by_contra h; simp [h] at ha
      subst this
      rw [walk_fullHist_snoc]
      simpa using hstop

end ThresholdHC.ReservoirTermination
