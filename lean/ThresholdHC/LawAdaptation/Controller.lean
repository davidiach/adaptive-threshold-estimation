import ThresholdHC.LawAdaptation.Execution
import ThresholdHC.Anytime.Full

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.LawAdaptation
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.Anytime
open ThresholdHC.BlindUpper ThresholdHC.ObservableSimulation

/-- Read a paid prefix, then choose a continuation using that observed prefix. -/
def thenChoose (n : ℕ) (p : Reader) (q : List Bool → Reader) (xs : List Bool) : ℕ :=
  if xs.length < n then p xs else q (xs.take n) (xs.drop n)

theorem readBlock_thenChoose (n m : ℕ) (p : Reader) (q : List Bool → Reader) (s : Table) :
    readBlock (n+m) (thenChoose n p q) s =
      let v := readBlock n p s
      let u := readBlock m (q v.1) v.2
      (v.1++u.1,u.2) := by
  induction n generalizing p q s with
  | zero =>
    have he : thenChoose 0 p q = q [] := by funext xs; simp [thenChoose]
    simp [he,readBlock]
  | succ n ih =>
    let i := p []
    let b := s i 0
    have he : (fun xs => thenChoose (n+1) p q (b::xs)) =
        thenChoose n (fun xs => p (b::xs)) (fun ys => q (b::ys)) := by
      funext xs
      simp [thenChoose]
    have hj : thenChoose (n+1) p q [] = i := by simp [thenChoose,i]
    rw [Nat.succ_add,readBlock,hj]
    change (b::(readBlock (n+m) (fun xs => thenChoose (n+1) p q (b::xs)) _).1,
      (readBlock (n+m) (fun xs => thenChoose (n+1) p q (b::xs)) _).2) = _
    rw [he,ih]
    rfl

variable {ι : Type} [Nonempty ι] {R : ι → ℕ → Type}
  [∀ i j, MeasurableSpace (R i j)]

def familySeedLaw (base : ∀ i j, AdaptiveEstimator (R i j)) : Measure (∀ i j, R i j) :=
  Measure.infinitePi (fun i => Measure.infinitePi (fun j => (base i j).randomLaw))

instance familySeedLaw_probability (base : ∀ i j, AdaptiveEstimator (R i j)) :
    IsProbabilityMeasure (familySeedLaw base) := by
  unfold familySeedLaw
  infer_instance

def postReader (laws : ι → Measure Gap) (n m : ℕ) (η : ℝ)
    (base : ∀ i j, AdaptiveEstimator (R i j)) (r : ∀ i j, R i j) (k : ℕ) : Reader :=
  thenChoose (pilotCost n m) (pilotReader m n) fun xs =>
    let i := chosenWord laws n m η xs
    fun ys => n + planReader (base i) (r i) k ys

def postHistoryInterval (laws : ι → Measure Gap) (n m : ℕ) (η M : ℝ)
    (base : ∀ i j, AdaptiveEstimator (R i j)) (rad : ι → ℕ → ℝ)
    (r : ∀ i j, R i j) (k : ℕ) (xs : List Bool) : ℝ × ℝ :=
  let i := chosenWord laws n m η (xs.take (pilotCost n m))
  historyInterval (base i) M (rad i) (r i) k (xs.drop (pilotCost n m))

def postTableInterval (laws : ι → Measure Gap) (n m : ℕ) (η M : ℝ)
    (base : ∀ i j, AdaptiveEstimator (R i j)) (rad : ι → ℕ → ℝ)
    (r : ∀ i j, R i j) (s : Table) (k : ℕ) : ℝ × ℝ :=
  let i := chosenTable laws n m η s
  tableInterval (base i) M (rad i) (r i) (s ∘ Nat.add n) k

theorem measurable_postReader (laws : ι → Measure Gap) (n m : ℕ) (η : ℝ)
    (base : ∀ i j, AdaptiveEstimator (R i j)) (k : ℕ) (xs : List Bool) :
    Measurable (fun r => postReader laws n m η base r k xs) := by
  by_cases h : xs.length < pilotCost n m
  · simp only [postReader,thenChoose,ite_eq_left h]
    exact measurable_const
  · simp only [postReader,thenChoose,ite_eq_right h]
    exact (measurable_of_countable (Nat.add n)).comp
      ((measurable_planReader _ k _).comp (measurable_pi_apply _))

theorem measurable_postHistoryInterval (laws : ι → Measure Gap) (n m : ℕ) (η M : ℝ)
    (base : ∀ i j, AdaptiveEstimator (R i j)) (rad : ι → ℕ → ℝ)
    (k : ℕ) (xs : List Bool) :
    Measurable (fun r => postHistoryInterval laws n m η M base rad r k xs) :=
  (measurable_historyInterval _ M _ k _).comp (measurable_pi_apply _)

def postEndpoint (laws : ι → Measure Gap) (n m : ℕ) (η M : ℝ)
    (base : ∀ i j, AdaptiveEstimator (R i j)) (rad : ι → ℕ → ℝ)
    (k : ℕ) (upper : Bool) : AdaptiveEstimator (∀ i j, R i j) where
  randomLaw := familySeedLaw base
  probability := inferInstance
  policy r := stopAt (pilotCost n m+paid k) (postReader laws n m η base r k)
  policy_measurable := by
    intro xs a
    by_cases h : xs.length < pilotCost n m+paid k
    · simp only [stopAt,ite_eq_left h]
      exact measurableSet_eq_fun ((measurable_of_countable some).comp
        (measurable_postReader laws n m η base k xs)) measurable_const
    · simp [stopAt,h]
  output z :=
    let I := postHistoryInterval laws n m η M base rad z.1 k
      (processHistory z.2 (pilotCost n m+paid k))
    if upper then I.2 else I.1
  output_measurable := by
    have hm : Measurable (fun z : (∀ i j, R i j) × List Bool =>
        postHistoryInterval laws n m η M base rad z.1 k z.2) :=
      measurable_from_prod_countable_left
        (measurable_postHistoryInterval laws n m η M base rad k)
    have ht := hm.comp (measurable_fst.prodMk
      ((measurable_processHistory_fixed (pilotCost n m+paid k)).comp measurable_snd))
    cases upper
    · exact ht.fst
    · exact ht.snd

/-- Selection never violates the physical cap, even on a misidentification path. -/
theorem postEndpoint_cap (laws : ι → Measure Gap) (n m : ℕ) (η M : ℝ)
    (base : ∀ i j, AdaptiveEstimator (R i j)) (rad : ι → ℕ → ℝ)
    (k : ℕ) (upper : Bool) :
    PathwiseCap (postEndpoint laws n m η M base rad k upper) (pilotCost n m+paid k) :=
  stopAt_pathwise_cap _ _ _ (fun _ => rfl)

/-- After the paid pilot, the selected reader uses fresh labels and its
observed output agrees with the selected table-level interval. -/
theorem postInterval_readBlock (laws : ι → Measure Gap) (n m : ℕ) (η M : ℝ)
    (base : ∀ i j, AdaptiveEstimator (R i j)) (rad : ι → ℕ → ℝ)
    (r : ∀ i j, R i j) (s : Table) (k : ℕ) :
    postHistoryInterval laws n m η M base rad r k
      (readBlock (pilotCost n m+paid k) (postReader laws n m η base r k) s).1 =
      postTableInterval laws n m η M base rad r s k := by
  let v := readBlock (pilotCost n m) (pilotReader m n) s
  let i := chosenTable laws n m η s
  let p := planReader (base i) (r i) k
  let u := readBlock (paid k) (Nat.add n ∘ p) v.2
  have hchosen : chosenWord laws n m η v.1 = i := chosenWord_readBlock laws n m η s
  have hword : (readBlock (pilotCost n m+paid k) (postReader laws n m η base r k) s).1 =
      v.1++u.1 := by
    unfold postReader
    rw [readBlock_thenChoose]
    dsimp only
    rw [hchosen]
    rfl
  have hlen : v.1.length = pilotCost n m := readBlock_length _ _ _
  have hfresh : v.2 ∘ Nat.add n = s ∘ Nat.add n := by
    funext j
    exact pilot_fresh m n (n+j) s (Nat.le_add_right _ _)
  have hcut := readBlock_relabel (paid k) (Nat.add n)
    (fun _ _ h => Nat.add_left_cancel h) p v.2
  rw [hfresh] at hcut
  change u.1 = _ at hcut
  unfold postHistoryInterval
  rw [hword,← hlen,List.take_left,List.drop_left,hchosen,hcut]
  exact interval_readBlock (base i) M (rad i) (r i) (s ∘ Nat.add n) k

theorem postEndpoint_output (laws : ι → Measure Gap) (n m : ℕ) (η M : ℝ)
    (base : ∀ i j, AdaptiveEstimator (R i j)) (rad : ι → ℕ → ℝ)
    (k : ℕ) (upper : Bool) (r : ∀ i j, R i j) (s : Table) :
    (postEndpoint laws n m η M base rad k upper).output
      (r,populationPath ((postEndpoint laws n m η M base rad k upper).policy r) s) =
      if upper then (postTableInterval laws n m η M base rad r s k).2
      else (postTableInterval laws n m η M base rad r s k).1 := by
  let w := (readBlock (pilotCost n m+paid k) (postReader laws n m η base r k) s).1
  have hp := block_path (pilotCost n m+paid k) (postReader laws n m η base r k) s
  change populationPath ((postEndpoint laws n m η M base rad k upper).policy r) s =
    fun i => w[i]? at hp
  change (if upper then (postHistoryInterval laws n m η M base rad r k
      (processHistory _ (pilotCost n m+paid k))).2
    else (postHistoryInterval laws n m η M base rad r k
      (processHistory _ (pilotCost n m+paid k))).1) = _
  rw [hp,← show w.length = pilotCost n m+paid k from readBlock_length _ _ _,
    processHistory_word,postInterval_readBlock laws n m η M base rad r s k]

end ThresholdHC.LawAdaptation

