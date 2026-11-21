import ThresholdHC.LargeBudgetRMS.RevisitPolicy
import ThresholdHC.LargeBudgetRMS.RevisitKernel

noncomputable section
namespace ThresholdHC.RevisitUpper
open Tier3 Tier5 Proofs ThresholdHC.SharpRMS.Revisit

def policy := HardBudget.stopAt 25 label

/-- The exact next-observation kernel on every supported history up to the budget. -/
theorem history_step {n : ℕ} (hn : n<25) (p : ℝ) (hp : p∈Set.Icc 0 1) (w : Prefix n)
    (nz : law policy p w≠0) (o : Option Bool) :
    let xs := fullHist w
    law policy p (Fin.snoc w o)=law policy p w*
      obsProb (nextHead p (if n<20 then none else mode ((xs.take 20).count true))) o := by
  obtain ⟨u,rfl⟩ := valid_word label hn.le p hp w nz
  let xs := List.ofFn u
  have len : xs.length=n := List.length_ofFn
  have act : policy (fullHist (fun i => some (u i)))=some (label xs) := by
    simp [policy,HardBudget.stopAt,full_bits,xs,hn]
  have prev (j : Fin n) : policy (histBefore (fun i => some (u i)) j)=some (label (xs.take j.val)) := by
    rw [hist_bits]
    simp [policy,HardBudget.stopAt,xs,show j.val<25 from j.isLt.trans hn]
  have early (j : Fin n) (hj : j.val<20) : label (xs.take j.val)=j.val := by
    simp [label,len,hj]
  by_cases pil : n<20
  · have lbl : label xs=n := by simp [label,len,pil]
    have hist (j : Fin n) : policy (histBefore (fun i => some (u i)) j)=some (label xs) ↔ (none : Option (Fin n))=some j := by
      rw [prev,early j (j.isLt.trans pil),lbl]
      simp [j.isLt.ne]
    simpa only [ite_eq_left pil,Option.bind_none] using step policy p hp _ _ act none hist o
  have phase : 20≤n := by omega
  let v := xs.take 20
  let k := n-20
  have hv : v.length=20 := by simp [v,len,phase]
  have hk : k<5 := by dsimp [k]; omega
  have lbl : label xs=follow v k := by simp [label,len,pil,v,k]
  have late (j : Fin n) (hj : 20≤j.val) : label (xs.take j.val)=follow v (j.val-20) := by
    simp [label,List.take_take,len,min_eq_left hj,not_lt.mpr hj,v]
  have distinct (j : Fin n) (hj : 20≤j.val) : label (xs.take j.val)≠label xs := by
    rw [late j hj,lbl]
    intro e
    have eq := follow_inj v e
    dsimp only [k] at eq
    omega
  rcases follow_mode v hv k hk with ⟨md,id⟩ | ⟨b,md,old,bit⟩
  · have hist (j : Fin n) : policy (histBefore (fun i => some (u i)) j)=some (label xs) ↔ (none : Option (Fin n))=some j := by
      rw [prev]
      by_cases h : j.val<20
      · rw [early j h,lbl,id]; simp; omega
      · simp [distinct j (by omega)]
    simpa only [ite_eq_right pil,full_bits,show mode (((List.ofFn u).take 20).count true)=none from md,Option.bind_none]
      using step policy p hp _ _ act none hist o
  · let a : Fin n := ⟨follow v k,by omega⟩
    have val : u a=b := by
      have ha : a.val<20 := old
      have eq : v[a.val]?=some (u a) := by
        rw [show v=xs.take 20 from rfl,List.getElem?_take_of_lt ha,List.getElem?_eq_getElem (by rw [len]; exact a.isLt)]
        simp [xs]
      exact Option.some.inj (eq.symm.trans bit)
    have hist (j : Fin n) : policy (histBefore (fun i => some (u i)) j)=some (label xs) ↔ some a=some j := by
      rw [prev]
      by_cases h : j.val<20
      · rw [early j h,lbl]
        simp only [Option.some.injEq,Fin.ext_iff]; exact eq_comm
      · have ne : a≠j := by intro e; have := congrArg Fin.val e; dsimp [a] at this; omega
        simp [ne,distinct j (by omega)]
    simpa only [ite_eq_right pil,full_bits,show mode (((List.ofFn u).take 20).count true)=some b from md,Option.bind_some,val]
      using step policy p hp _ _ act (some a) hist o

end ThresholdHC.RevisitUpper
