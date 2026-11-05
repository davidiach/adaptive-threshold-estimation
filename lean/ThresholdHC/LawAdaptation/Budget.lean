import ThresholdHC.LawAdaptation.Controller

noncomputable section
open MeasureTheory
namespace ThresholdHC.LawAdaptation
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.Anytime
open ThresholdHC.BlindUpper ThresholdHC.ObservableSimulation

variable {ι : Type} [Nonempty ι] {R : ι → ℕ → Type}
  [∀ i j, MeasurableSpace (R i j)]

/-- During the pilot, report the full parameter range and pause at the budget. -/
def pilotEndpoint (base : ∀ i j, AdaptiveEstimator (R i j)) (n m B : ℕ)
    (M : ℝ) (upper : Bool) : AdaptiveEstimator (∀ i j, R i j) where
  randomLaw := familySeedLaw base
  probability := inferInstance
  policy _ := stopAt B (pilotReader m n)
  policy_measurable := by
    intro xs a
    exact measurableSet_eq_fun measurable_const measurable_const
  output _ := if upper then M else 0
  output_measurable := measurable_const

def budgetEndpoint (laws : ι → Measure Gap) (n m : ℕ) (η M : ℝ)
    (base : ∀ i j, AdaptiveEstimator (R i j)) (rad : ι → ℕ → ℝ)
    (B : ℕ) (upper : Bool) : AdaptiveEstimator (∀ i j, R i j) :=
  if pilotCost n m ≤ B then
    postEndpoint laws n m η M base rad (stageCount ((B-pilotCost n m:ℕ):ℝ)) upper
  else pilotEndpoint base n m B M upper

def budgetInterval (laws : ι → Measure Gap) (n m : ℕ) (η M : ℝ)
    (base : ∀ i j, AdaptiveEstimator (R i j)) (rad : ι → ℕ → ℝ)
    (B : ℕ) (z : (∀ i j, R i j) × Table) : ℝ × ℝ :=
  let x := populationPath ((budgetEndpoint laws n m η M base rad B false).policy z.1) z.2
  ((budgetEndpoint laws n m η M base rad B false).output (z.1,x),
    (budgetEndpoint laws n m η M base rad B true).output (z.1,x))

theorem budgetEndpoint_cap (laws : ι → Measure Gap) (n m : ℕ) (η M : ℝ)
    (base : ∀ i j, AdaptiveEstimator (R i j)) (rad : ι → ℕ → ℝ)
    (B : ℕ) (upper : Bool) :
    PathwiseCap (budgetEndpoint laws n m η M base rad B upper) B := by
  by_cases h : pilotCost n m ≤ B
  · rw [budgetEndpoint,ite_eq_left h]
    intro r x hx
    apply (postEndpoint_cap laws n m η M base rad _ upper r x hx).trans
    have hp := paid_fits ((B-pilotCost n m:ℕ):ℝ)
    rw [Nat.floor_natCast] at hp
    exact_mod_cast (show pilotCost n m+paid (stageCount ((B-pilotCost n m:ℕ):ℝ)) ≤ B by omega)
  · rw [budgetEndpoint,ite_eq_right h]
    exact stopAt_pathwise_cap _ _ _ (fun _ => rfl)

theorem budgetInterval_eq (laws : ι → Measure Gap) (n m : ℕ) (η M : ℝ)
    (base : ∀ i j, AdaptiveEstimator (R i j)) (rad : ι → ℕ → ℝ)
    (B : ℕ) (z : (∀ i j, R i j) × Table) :
    budgetInterval laws n m η M base rad B z =
      if pilotCost n m ≤ B then postTableInterval laws n m η M base rad z.1 z.2
        (stageCount ((B-pilotCost n m:ℕ):ℝ)) else (0,M) := by
  by_cases h : pilotCost n m ≤ B
  · simp only [budgetInterval,budgetEndpoint,ite_eq_left h]
    rw [postEndpoint_output,
      show (postEndpoint laws n m η M base rad _ false).policy =
        (postEndpoint laws n m η M base rad _ true).policy from rfl,postEndpoint_output]
    rfl
  · simp only [budgetInterval,budgetEndpoint,ite_eq_right h]
    rfl

theorem measurable_budgetInterval (laws : ι → Measure Gap) (n m : ℕ) (η M : ℝ)
    (base : ∀ i j, AdaptiveEstimator (R i j)) (rad : ι → ℕ → ℝ) (B : ℕ) :
    Measurable (budgetInterval laws n m η M base rad B) := by
  let A := budgetEndpoint laws n m η M base rad B false
  have hm : Measurable (fun z : (∀ i j, R i j) × Table =>
      (z.1,populationPath (A.policy z.1) z.2)) :=
    measurable_fst.prodMk (measurable_seeded_populationPath A.policy
      (fun xs => measurable_to_countable' (A.policy_measurable xs)))
  exact (A.output_measurable.comp hm).prodMk
    ((budgetEndpoint laws n m η M base rad B true).output_measurable.comp hm)

theorem stageCount_nat_mono {a b : ℕ} (hab : a ≤ b) :
    stageCount (a:ℝ) ≤ stageCount (b:ℝ) := by
  have ha := paid_fits (a:ℝ)
  have hb := next_exceeds (b:ℝ)
  rw [Nat.floor_natCast] at ha hb
  by_contra h
  have hn : stageCount (b:ℝ)+1 ≤ stageCount (a:ℝ) := by omega
  have hp := paid_strict.monotone hn
  omega

theorem postReader_compatible (laws : ι → Measure Gap) (n m : ℕ) (η : ℝ)
    (base : ∀ i j, AdaptiveEstimator (R i j)) (r : ∀ i j, R i j)
    {k l : ℕ} (hkl : k ≤ l) (xs : List Bool) (hx : xs.length < pilotCost n m+paid k) :
    postReader laws n m η base r l xs = postReader laws n m η base r k xs := by
  by_cases h : xs.length < pilotCost n m
  · simp only [postReader,thenChoose,ite_eq_left h]
  · simp only [postReader,thenChoose,ite_eq_right h]
    congr 1
    apply planReader_compatible _ _ hkl
    rw [List.length_drop]
    omega

/-- Larger budgets extend exactly the same pilot and selected stage history.
The compatibility claim holds on all histories, even incorrect selections. -/
theorem budget_policy_compatible (laws : ι → Measure Gap) (n m : ℕ) (η M : ℝ)
    (base : ∀ i j, AdaptiveEstimator (R i j)) (rad : ι → ℕ → ℝ)
    {B C : ℕ} (hBC : B ≤ C) (upper upper' : Bool) (r : ∀ i j, R i j)
    (xs : List Bool)
    (hx : xs.length < if pilotCost n m ≤ B then
      pilotCost n m+paid (stageCount ((B-pilotCost n m:ℕ):ℝ)) else B) :
    (budgetEndpoint laws n m η M base rad C upper').policy r xs =
      (budgetEndpoint laws n m η M base rad B upper).policy r xs := by
  by_cases hB : pilotCost n m ≤ B
  · have hC := hB.trans hBC
    simp only [ite_eq_left hB] at hx
    have hk := stageCount_nat_mono (Nat.sub_le_sub_right hBC (pilotCost n m))
    have hl : xs.length < pilotCost n m+paid (stageCount ((C-pilotCost n m:ℕ):ℝ)) :=
      hx.trans_le (Nat.add_le_add_left (paid_strict.monotone hk) _)
    simp only [budgetEndpoint,ite_eq_left hB,ite_eq_left hC,postEndpoint,
      stopAt,ite_eq_left hx,ite_eq_left hl]
    exact congrArg some (postReader_compatible laws n m η base r hk xs hx)
  · simp only [ite_eq_right hB] at hx
    have hpilot : xs.length < pilotCost n m := by omega
    by_cases hC : pilotCost n m ≤ C
    · have hl : xs.length < pilotCost n m+paid (stageCount ((C-pilotCost n m:ℕ):ℝ)) := by omega
      simp only [budgetEndpoint,ite_eq_right hB,ite_eq_left hC,postEndpoint,pilotEndpoint,
        stopAt,ite_eq_left hx,ite_eq_left hl,postReader,thenChoose,ite_eq_left hpilot]
    · have hl : xs.length < C := hx.trans_le hBC
      simp only [budgetEndpoint,ite_eq_right hB,ite_eq_right hC,pilotEndpoint,
        stopAt,ite_eq_left hx,ite_eq_left hl]

end ThresholdHC.LawAdaptation

