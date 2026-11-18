import PilotPolicy

/-! A fixed seven-action schedule may depend on every bit of the pilot. -/
namespace PilotFeedback.Ordered
noncomputable section
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Proofs ThresholdHC.SharpRMS
open ThresholdHC.SharpRMS.Revisit ThresholdHC.SharpRMS.Pilot

abbrev Schedule := List Bool → ℕ → Option Bool

def effective (A : Schedule) (v : List Bool) (k : ℕ) :=
  Pilot.choice (fun _ _ => A v k) (v.count true) k 0

def label (A : Schedule) (xs : List Bool) : ℕ :=
  if xs.length<18 then xs.length else
    let v := xs.take 18
    pick v (xs.length-18) (effective A v (xs.length-18))

def policy (A : Schedule) := HardBudget.stopAt 25 (label A)

def action (A : Schedule) (xs : List Bool) : Option Bool :=
  if xs.length<18 then none else effective A (xs.take 18) (xs.length-18)

private theorem picks_distinct (v : List Bool) (hv : v.length=18) {k l : ℕ} (kl : k≠l)
    (x y : Option Bool) (hx : ∀ b, x=some b → k<available (v.count true) b)
    (hy : ∀ b, y=some b → l<available (v.count true) b) : pick v k x≠pick v l y := by
  intro eq
  cases x with
  | none =>
    cases y with
    | none => simp [pick] at eq; contradiction
    | some d => have := (pick_old v hv l d (hy d rfl)).1; change 18+k=pick v l (some d) at eq; omega
  | some b =>
    have hk := pick_old v hv k b (hx b rfl)
    cases y with
    | none => change pick v k (some b)=18+l at eq; omega
    | some d =>
      have hl := pick_old v hv l d (hy d rfl)
      have same : b=d := Option.some.inj (hk.2.symm.trans ((congrArg (fun i : ℕ => v[i]?) eq).trans hl.2))
      subst d
      have k' : k<(candidates v b).card := by rw [candidates_count v hv]; exact hx b rfl
      have l' : l<(candidates v b).card := by rw [candidates_count v hv]; exact hy b rfl
      simp only [pick,dite_eq_left k',dite_eq_left l'] at eq
      exact kl (congrArg Fin.val (((candidates v b).orderEmbOfFin rfl).injective (Fin.ext eq)))

theorem history_step (A : Schedule) {n : ℕ} (hn : n<25) (p : ℝ) (hp : p∈Set.Icc 0 1) (w : Prefix n)
    (nz : law (policy A) p w≠0) (o : Option Bool) :
    law (policy A) p (Fin.snoc w o)=law (policy A) p w*obsProb (nextHead p (action A (fullHist w))) o := by
  obtain ⟨u,rfl⟩ := valid_word (label A) hn.le p hp w nz
  let xs := List.ofFn u
  have len : xs.length=n := List.length_ofFn
  have act : policy A (fullHist (fun i => some (u i)))=some (label A xs) := by
    simp [policy,HardBudget.stopAt,full_bits,xs,hn]
  have prev (j : Fin n) : policy A (histBefore (fun i => some (u i)) j)=some (label A (xs.take j.val)) := by
    rw [hist_bits]
    simp [policy,HardBudget.stopAt,xs,show j.val<25 from j.isLt.trans hn]
  have early (j : Fin n) (hj : j.val<18) : label A (xs.take j.val)=j.val := by simp [label,len,hj]
  rw [full_bits]
  by_cases pil : n<18
  · have lbl : label A xs=n := by simp [label,len,pil]
    have hist (j : Fin n) : policy A (histBefore (fun i => some (u i)) j)=some (label A xs) ↔ (none : Option (Fin n))=some j := by
      rw [prev,early j (j.isLt.trans pil),lbl]; simp [j.isLt.ne]
    simpa only [action,List.length_ofFn,ite_eq_left pil,Option.bind_none] using step (policy A) p hp _ _ act none hist o
  let v := xs.take 18
  let k := n-18
  have ge : 18≤n := by omega
  have hv : v.length=18 := by simp [v,len,ge]
  let md := effective A v k
  have lbl : label A xs=pick v k md := by simp [label,len,pil,v,k,md]
  have mode_eq : action A (List.ofFn u)=md := by simp [action,xs,v,k,md,len,pil]
  rw [mode_eq]
  have distinct (j : Fin n) (hj : 18≤j.val) : label A (xs.take j.val)≠label A xs := by
    rw [lbl]
    simp only [label,List.length_take,len,min_eq_left j.isLt.le,not_lt.mpr hj,ite_false,
      List.take_take,min_eq_left hj]
    apply picks_distinct v hv (show j.val-18≠k by dsimp [k]; omega)
    · exact fun b h => Pilot.choice_available _ h
    · exact fun b h => Pilot.choice_available _ h
  cases hm : md with
  | none =>
    have id : label A xs=18+k := by rw [lbl,hm]; rfl
    have hist (j : Fin n) : policy A (histBefore (fun i => some (u i)) j)=some (label A xs) ↔ (none : Option (Fin n))=some j := by
      rw [prev]
      by_cases h : j.val<18
      · rw [early j h,id]; simp; omega
      · simp [distinct j (by omega)]
    simpa only [Option.bind_none] using step (policy A) p hp _ _ act none hist o
  | some b =>
    have ok := pick_old v hv k b (Pilot.choice_available _ hm)
    have old : label A xs<18 := by simpa [lbl,hm] using ok.1
    let a : Fin n := ⟨label A xs,by omega⟩
    have val : u a=b := by
      have ha : a.val<18 := old
      have eq : v[a.val]?=some (u a) := by
        rw [show v=xs.take 18 from rfl,List.getElem?_take_of_lt ha,List.getElem?_eq_getElem (by rw [len]; exact a.isLt)]
        simp [xs]
      exact Option.some.inj (eq.symm.trans (by simpa [a,lbl,hm] using ok.2))
    have hist (j : Fin n) : policy A (histBefore (fun i => some (u i)) j)=some (label A xs) ↔ some a=some j := by
      rw [prev]
      by_cases h : j.val<18
      · rw [early j h]; simp only [Option.some.injEq,Fin.ext_iff]; exact eq_comm
      · have ne : a≠j := by intro e; have := congrArg Fin.val e; dsimp [a] at this; omega
        simp [ne,distinct j (by omega)]
    simpa only [Option.bind_some,val] using step (policy A) p hp _ _ act (some a) hist o


end
end PilotFeedback.Ordered
