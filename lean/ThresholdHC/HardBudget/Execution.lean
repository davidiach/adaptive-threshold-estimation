import ThresholdHC.HardBudget.Stage

noncomputable section
namespace ThresholdHC.HardBudget
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper

variable {R : ℕ → Type} [∀ j, MeasurableSpace (R j)]

def paid (k : ℕ) : ℕ := match k with
  | 0 => 0
  | j+1 => paid j + stageCap j

def planReader (base : ∀ j, AdaptiveEstimator (R j)) (r : ∀ j, R j) : ℕ → Reader
  | 0 => fun _ => 0
  | j+1 => thenRead (paid j) (planReader base r j)
      (Nat.pair j ∘ fun h => ((base j).policy (r j) h).getD 0)

def planOutput (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (r : ∀ j, R j) :
    ℕ → List Bool → ℝ
  | 0, _ => M/2
  | j+1, xs => (stageOutput (base j) M (r j) (xs.drop (paid j))).getD
      (planOutput base M r j (xs.take (paid j)))

private theorem reader_range (base : ∀ j, AdaptiveEstimator (R j)) (r : ∀ j, R j)
    (n : ℕ) (h : 0 < n) (xs : List Bool) :
    ∃ i < n, ∃ k, planReader base r n xs = Nat.pair i k := by
  induction n generalizing xs with
  | zero => omega
  | succ n ih =>
    by_cases hz : xs.length < paid n
    · have hn : 0 < n := by
        cases n with
        | zero => simp [paid] at hz
        | succ n => omega
      obtain ⟨i,hi,k,hk⟩ := ih hn xs
      exact ⟨i,by omega,k,by simpa only [planReader,thenRead,ite_eq_left hz] using hk⟩
    · exact ⟨n,by omega,((base n).policy (r n) (xs.drop (paid n))).getD 0,by simp [planReader,thenRead,hz]⟩

theorem next_stage_fresh (base : ∀ j, AdaptiveEstimator (R j)) (r : ∀ j, R j) (n : ℕ)
    (s : Table) (c : ℕ) :
    (readBlock (paid n) (planReader base r n) s).2 (Nat.pair n c) = s (Nat.pair n c) := by
  cases n with
  | zero => rfl
  | succ n =>
    apply readBlock_untouched
    intro xs h
    obtain ⟨i,hi,j,hj⟩ := reader_range base r (n+1) (Nat.zero_lt_succ _) xs
    have hfirst := (Nat.pair_eq_pair.mp (hj.symm.trans h)).1
    omega

/-- A controller using disjoint physical labels returns precisely the latest
completed clipped estimate, independently of the filler observations. -/
theorem planOutput_readBlock (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ)
    (r : ∀ j, R j) (s : Table) (k : ℕ) :
    planOutput base M r k (readBlock (paid k) (planReader base r k) s).1 =
      idealFallback base M r s k := by
  induction k with
  | zero => rfl
  | succ j ih =>
    let p := planReader base r j
    let v := readBlock (paid j) p s
    let q := fun h => ((base j).policy (r j) h).getD 0
    let stage := readBlock (stageCap j) (Nat.pair j ∘ q) v.2
    have hword : (readBlock (paid (j+1)) (planReader base r (j+1)) s).1 = v.1++stage.1 :=
      congrArg Prod.fst (readBlock_append (paid j) (stageCap j) p (Nat.pair j ∘ q) s)
    have hlen : v.1.length = paid j := readBlock_length _ _ _
    have hcut := readBlock_relabel (stageCap j) (Nat.pair j) (fun a b hab =>
      (Nat.pair_eq_pair.mp hab).2) q v.2
    have he : v.2 ∘ Nat.pair j = s ∘ Nat.pair j := funext (next_stage_fresh base r j s)
    rw [he] at hcut
    change stage.1 = _ at hcut
    rw [planOutput,hword,← hlen,List.drop_left,List.take_left,hcut]
    exact congrArg₂ Option.getD (stageOutput_correct (base j) M (stageCap j) (r j) (s ∘ Nat.pair j)) ih

end ThresholdHC.HardBudget
