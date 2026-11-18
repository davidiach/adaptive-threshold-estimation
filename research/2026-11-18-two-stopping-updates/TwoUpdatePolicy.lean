import OrderedExperiment

namespace PilotFeedback.TwoUpdates
noncomputable section
open Ordered ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.SharpRMS
open ThresholdHC.SharpRMS.Revisit

/-- Both triggers read the observed history. The second trigger and final
schedule can also use the prefix at which the first replacement occurred. -/
structure Plan where
  first : Ordered.Schedule
  trigger₁ : List Bool → Bool
  middle : Ordered.Schedule
  trigger₂ : List Bool → List Bool → Bool
  last : List Bool → Ordered.Schedule

inductive Stage where
  | initial
  | middle (firstWord : List Bool)
  | final (firstWord secondWord : List Bool)

def update (P : Plan) (s : Stage) (xs : List Bool) : Stage :=
  if xs.length < 18 then s else
    match s with
    | .initial => if P.trigger₁ xs then .middle xs else .initial
    | .middle z => if P.trigger₂ z xs then .final z xs else .middle z
    | .final z u => .final z u

def schedule (P : Plan) (v : List Bool) : Stage → ℕ → Option Bool
  | .initial => P.first v
  | .middle z => P.middle z
  | .final z u => P.last z u

/-- The stage just before the decision at prefix length n. -/
def before (P : Plan) (word : List Bool) : ℕ → Stage
  | 0 => .initial
  | n+1 => update P (before P word n) (word.take n)

theorem before_take (P : Plan) (xs : List Bool) {n l : ℕ} (h : n≤l) :
    before P (xs.take l) n = before P xs n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [before,ih (by omega),List.take_take,min_eq_left (by omega : n≤l)]

theorem before_snoc (P : Plan) (xs : List Bool) (b : Bool) :
    before P (xs++[b]) (xs++[b]).length = update P (before P xs xs.length) xs := by
  simp only [List.length_append,List.length_singleton,before,List.take_left]
  rw [←before_take P (xs++[b]) (n := xs.length) (l := xs.length) (le_refl _),List.take_left]

theorem pilot_stage (P : Plan) (xs : List Bool) (n : ℕ) (h : n≤18) : before P xs n = .initial := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have lt : (xs.take n).length<18 := by simp only [List.length_take]; omega
    simp only [before,ih (by omega),update,lt,↓reduceIte]

def frozen (P : Plan) (word : List Bool) : Ordered.Schedule := fun v k =>
  schedule P v (update P (before P word (18+k)) (word.take (18+k))) k

def label (P : Plan) (xs : List Bool) := Ordered.label (frozen P xs) xs
def policy (P : Plan) := HardBudget.stopAt 25 (label P)
def action (P : Plan) (xs : List Bool) := Ordered.action (frozen P xs) xs

private theorem label_take (P : Plan) (xs : List Bool) (l : ℕ) :
    label P (xs.take l) = Ordered.label (frozen P xs) (xs.take l) := by
  unfold label Ordered.label
  split
  · rfl
  · let v := (xs.take l).take 18
    let k := (xs.take l).length-18
    apply congrArg (Pilot.pick v k)
    change effective (frozen P (xs.take l)) v k = effective (frozen P xs) v k
    have h : 18+k≤l := by dsimp [k]; simp only [List.length_take] at *; omega
    simp only [effective,Pilot.choice,frozen,before_take P xs h,List.take_take,min_eq_left h]

private theorem law_congr {n : ℕ} (p : ℝ) (w : Prefix n) (F G : List Bool → Option ℕ)
    (h : ∀ j, F (histBefore w j) = G (histBefore w j)) : law F p w = law G p w := by
  let m := max (coinCap n F) (coinCap n G)
  unfold law
  rw [creationLaw_eq_capped F _ _ w m (le_max_left ..),creationLaw_eq_capped G _ _ w m (le_max_right ..)]
  have capped (j) : capPolicy m F (histBefore w j) = capPolicy m G (histBefore w j) := by simp only [capPolicy,h]
  simp_rw [transcriptLaw_factor,pathValidity,coinLike,capped]

set_option maxHeartbeats 4000000 in
theorem history_step (P : Plan) {n : ℕ} (hn : n<25) (p : ℝ) (hp : p∈Set.Icc 0 1) (w : Prefix n)
    (nz : law (policy P) p w ≠ 0) (o : Option Bool) :
    law (policy P) p (Fin.snoc w o) = law (policy P) p w * obsProb (nextHead p (action P (fullHist w))) o := by
  obtain ⟨u,rfl⟩ := valid_word (label P) hn.le p hp w nz
  let xs := List.ofFn u
  let s := frozen P xs
  have same (l : ℕ) : policy P (xs.take l) = Ordered.policy s (xs.take l) := by
    simp only [policy,Ordered.policy,HardBudget.stopAt,label_take P xs l,s]
  have prev (j : Fin n) : policy P (histBefore (fun i => some (u i)) j) =
      Ordered.policy s (histBefore (fun i => some (u i)) j) := by rw [hist_bits]; exact same j
  have current : policy P xs = Ordered.policy s xs := by rfl
  have pre := law_congr p (fun i => some (u i)) _ _ prev
  have extn := law_congr p (Fin.snoc (fun i => some (u i)) o) (policy P) (Ordered.policy s) (by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa only [histBefore_snoc_last,full_bits] using current
    · simpa only [histBefore_snoc_castSucc] using prev k)
  rw [extn,pre,Ordered.history_step s hn p hp _ (pre.symm ▸ nz),full_bits]
  rfl

/-- Conditional expectation with arbitrary output of the ordered word. -/
def run (P : Plan) (p : ℝ) (X : List Bool → ℝ) : ℕ → List Bool → ℝ
  | 0, xs => X xs
  | n+1, xs =>
    let r := nextHead p (action P xs)
    (1-r)*run P p X n (xs++[false]) + r*run P p X n (xs++[true])

theorem expect (A : Plan) (p : ℝ) (hp : p∈Set.Icc 0 1) (X : List Bool → ℝ) :
    (∑ w : Prefix 25, law (policy A) p w * X (fullHist w)) = run A p X 25 [] := by
  have H (n : ℕ) (hn : n≤25) :
      (∑ w : Prefix n, law (policy A) p w * run A p X (25-n) (fullHist w)) = run A p X 25 [] := by
    induction n with
    | zero => simp [law,creationLaw,transcriptLaw_factor,pathValidity,coinLike,fullHist]
    | succ n ih =>
      rw [sum_snoc,←ih (by omega)]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hz : law (policy A) p w = 0
      · have zero (o : Option Bool) : law (policy A) p (Fin.snoc w o) = 0 := by
          have pos (a) : 0 ≤ law (policy A) p (Fin.snoc w a) :=
            (creationLaw_total _ (policy A) _ _ (fun _ => by norm_num) (fun _ => hp)).1 _
          have eq := creationLaw_sum_extensions (policy A) (fun _ => 1/5) (fun _ => p) w
          exact le_antisymm ((Finset.single_le_sum (fun a _ => pos a) (Finset.mem_univ o)).trans (eq.trans hz).le) (pos o)
        simp [zero,hz]
      simp_rw [history_step A (by omega : n<25) p hp w hz]
      rw [show 25-n=(25-(n+1))+1 by omega,run]
      simp only [Fintype.sum_option,Fintype.sum_bool,obsProb,mul_zero,zero_mul,zero_add,fullHist_snoc_example,
        Option.toList_some]
      ring
  exact H 25 (by decide)

end
end PilotFeedback.TwoUpdates
