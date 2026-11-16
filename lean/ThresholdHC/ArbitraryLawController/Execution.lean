import ThresholdHC.ArbitraryLawAdaptation.LearnedStage
import ThresholdHC.Anytime.Compatibility
import ThresholdHC.HardBudget.Inputs

/-! Chronological execution of variable-length paid stages. Zero-length
stages buy no observations; reported intervals use the observed pilot word. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace ThresholdHC.ArbitraryLawController
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget
open ThresholdHC.BlindUpper ThresholdHC.ObservableSimulation
open ThresholdHC.ArbitraryLawAdaptation

variable {R : ℕ → Type} [∀ j, MeasurableSpace (R j)]

def spent (S : ∀ j, LearnedStage (R j)) : ℕ → ℕ
  | 0 => 0
  | j + 1 => spent S j + (S j).cap

def reader (S : ∀ j, LearnedStage (R j)) (r : ∀ j, R j) : ℕ → Reader
  | 0 => fun _ => 0
  | j + 1 => thenRead (spent S j) (reader S r j) (Nat.pair j ∘ (S j).reader (r j))

def intersect (I J : ℝ × ℝ) : ℝ × ℝ := (max I.1 J.1, min I.2 J.2)

def historyInterval (S : ∀ j, LearnedStage (R j)) (ρ : ℝ) (r : ∀ j, R j) :
    ℕ → List Bool → ℝ × ℝ
  | 0, _ => (0, ρ)
  | j + 1, xs => intersect (historyInterval S ρ r j (xs.take (spent S j)))
      ((S j).historyInterval (r j) (xs.drop (spent S j)))

def tableInterval (S : ∀ j, LearnedStage (R j)) (ρ : ℝ) (r : ∀ j, R j)
    (s : Table) : ℕ → ℝ × ℝ
  | 0 => (0, ρ)
  | j + 1 => intersect (tableInterval S ρ r s j) ((S j).tableInterval (r j) (s ∘ Nat.pair j))

theorem spent_mono (S : ∀ j, LearnedStage (R j)) : Monotone (spent S) := by
  apply monotone_nat_of_le_succ
  intro j
  exact Nat.le_add_right _ _

theorem spent_le_paid (S : ∀ j, LearnedStage (R j))
    (h : ∀ j, (S j).cap ≤ stageCap j) (k : ℕ) : spent S k ≤ paid k := by
  induction k with
  | zero => rfl
  | succ j ih => exact Nat.add_le_add ih (h j)

theorem measurable_reader (S : ∀ j, LearnedStage (R j)) (k : ℕ) (xs : List Bool) :
    Measurable (fun r => reader S r k xs) := by
  induction k generalizing xs with
  | zero => exact measurable_const
  | succ j ih =>
    by_cases h : xs.length < spent S j
    · simp only [reader, thenRead, ite_eq_left h]; exact ih xs
    · simp only [reader, thenRead, ite_eq_right h, Function.comp_apply]
      exact (measurable_of_countable (Nat.pair j)).comp
        (((S j).measurable_reader _).comp (measurable_pi_apply j))

theorem measurable_historyInterval (S : ∀ j, LearnedStage (R j)) (ρ : ℝ)
    (k : ℕ) (xs : List Bool) : Measurable (fun r => historyInterval S ρ r k xs) := by
  induction k generalizing xs with
  | zero => exact measurable_const
  | succ j ih =>
    have hp := ih (xs.take (spent S j))
    have hc := ((S j).measurable_historyInterval (xs.drop (spent S j))).comp (measurable_pi_apply j)
    exact (hp.fst.max hc.fst).prodMk (hp.snd.min hc.snd)

def endpoint (S : ∀ j, LearnedStage (R j)) (ρ : ℝ) (k : ℕ) (upper : Bool) :
    AdaptiveEstimator (∀ j, R j) where
  randomLaw := Measure.infinitePi (fun j => (S j).randomLaw)
  probability := by
    let (j : ℕ) : IsProbabilityMeasure (S j).randomLaw := (S j).probability
    infer_instance
  policy r := stopAt (spent S k) (reader S r k)
  policy_measurable := by
    intro xs a
    by_cases h : xs.length < spent S k
    · simp only [stopAt, ite_eq_left h]
      exact measurableSet_eq_fun ((measurable_of_countable some).comp (measurable_reader S k xs)) measurable_const
    · simp [stopAt, h]
  output z := let I := historyInterval S ρ z.1 k (processHistory z.2 (spent S k))
              if upper then I.2 else I.1
  output_measurable := by
    have hm : Measurable (fun z : (∀ j, R j) × List Bool => historyInterval S ρ z.1 k z.2) :=
      measurable_from_prod_countable_left (measurable_historyInterval S ρ k)
    have ht := hm.comp (measurable_fst.prodMk ((measurable_processHistory_fixed (spent S k)).comp measurable_snd))
    cases upper
    · exact ht.fst
    · exact ht.snd

theorem endpoint_cap (S : ∀ j, LearnedStage (R j)) (ρ : ℝ) (k : ℕ) (upper : Bool) :
    PathwiseCap (endpoint S ρ k upper) (spent S k) :=
  stopAt_pathwise_cap _ _ _ (fun _ => rfl)

theorem endpoint_budget_cap (S : ∀ j, LearnedStage (R j)) (ρ : ℝ)
    (h : ∀ j, (S j).cap ≤ stageCap j) (B : ℝ) (upper : Bool) :
    PathwiseCap (endpoint S ρ (stageCount B) upper) ⌊B⌋₊ := by
  intro r x hx
  exact (endpoint_cap S ρ _ upper r x hx).trans
    (Nat.cast_le.mpr ((spent_le_paid S h _).trans (paid_fits B)))

theorem reader_range (S : ∀ j, LearnedStage (R j)) (r : ∀ j, R j)
    (n : ℕ) (hn : 0 < n) (xs : List Bool) :
    ∃ i < n, ∃ c, reader S r n xs = Nat.pair i c := by
  induction n generalizing xs with
  | zero => omega
  | succ n ih =>
    by_cases h : xs.length < spent S n
    · have hn : 0 < n := by cases n <;> simp_all [spent]
      obtain ⟨i, hi, c, hc⟩ := ih hn xs
      exact ⟨i, by omega, c, by simpa only [reader, thenRead, ite_eq_left h] using hc⟩
    · exact ⟨n, by omega, (S n).reader (r n) (xs.drop (spent S n)), by simp [reader, thenRead, h]⟩

theorem next_stage_fresh (S : ∀ j, LearnedStage (R j)) (r : ∀ j, R j)
    (n : ℕ) (s : Table) (c : ℕ) :
    (readBlock (spent S n) (reader S r n) s).2 (Nat.pair n c) = s (Nat.pair n c) := by
  cases n with
  | zero => rfl
  | succ n =>
    apply readBlock_untouched
    intro xs h
    obtain ⟨i, hi, j, hj⟩ := reader_range S r (n + 1) (by omega) xs
    have := (Nat.pair_eq_pair.mp (hj.symm.trans h)).1
    omega

theorem interval_readBlock (S : ∀ j, LearnedStage (R j)) (ρ : ℝ)
    (r : ∀ j, R j) (s : Table) (k : ℕ) :
    historyInterval S ρ r k (readBlock (spent S k) (reader S r k) s).1 =
      tableInterval S ρ r s k := by
  induction k with
  | zero => rfl
  | succ j ih =>
    let v := readBlock (spent S j) (reader S r j) s
    let u := readBlock (S j).cap (Nat.pair j ∘ (S j).reader (r j)) v.2
    have hw : (readBlock (spent S (j + 1)) (reader S r (j + 1)) s).1 = v.1 ++ u.1 :=
      congrArg Prod.fst (readBlock_append _ _ _ _ s)
    have hl : v.1.length = spent S j := readBlock_length _ _ _
    have hu := readBlock_relabel (S j).cap (Nat.pair j)
      (fun _ _ h => (Nat.pair_eq_pair.mp h).2) ((S j).reader (r j)) v.2
    have hf : v.2 ∘ Nat.pair j = s ∘ Nat.pair j := funext (next_stage_fresh S r j s)
    rw [hf] at hu
    change u.1 = _ at hu
    rw [historyInterval, hw, ← hl, List.take_left, List.drop_left, hu]
    rw [show historyInterval S ρ r j v.1 = tableInterval S ρ r s j from ih,
      (S j).interval_readBlock]
    rfl

theorem endpoint_output (S : ∀ j, LearnedStage (R j)) (ρ : ℝ) (k : ℕ)
    (upper : Bool) (r : ∀ j, R j) (s : Table) :
    (endpoint S ρ k upper).output (r, populationPath ((endpoint S ρ k upper).policy r) s) =
      if upper then (tableInterval S ρ r s k).2 else (tableInterval S ρ r s k).1 := by
  let w := (readBlock (spent S k) (reader S r k) s).1
  have hp := block_path (spent S k) (reader S r k) s
  change populationPath ((endpoint S ρ k upper).policy r) s = fun i => w[i]? at hp
  change (if upper then (historyInterval S ρ r k (processHistory _ (spent S k))).2
    else (historyInterval S ρ r k (processHistory _ (spent S k))).1) = _
  rw [hp, ← show w.length = spent S k from readBlock_length _ _ _, processHistory_word,
    interval_readBlock]

theorem reader_compatible (S : ∀ j, LearnedStage (R j)) (r : ∀ j, R j)
    {k l : ℕ} (hkl : k ≤ l) (xs : List Bool) (hx : xs.length < spent S k) :
    reader S r l xs = reader S r k xs := by
  induction l with
  | zero =>
    have hk : k = 0 := by omega
    rw [hk]
  | succ l ih =>
    by_cases he : k = l + 1
    · rw [he]
    · have hk : k ≤ l := by omega
      have hl := hx.trans_le (spent_mono S hk)
      rw [reader, thenRead, ite_eq_left hl]
      exact ih hk

theorem word_prefix (S : ∀ j, LearnedStage (R j)) (r : ∀ j, R j)
    {k l : ℕ} (hkl : k ≤ l) (s : Table) :
    ((readBlock (spent S l) (reader S r l) s).1).take (spent S k) =
      (readBlock (spent S k) (reader S r k) s).1 :=
  Anytime.readBlock_prefix (spent_mono S hkl) _ _ s
    (fun xs hx => (reader_compatible S r hkl xs hx).symm)

theorem endpoint_policy_compatible (S : ∀ j, LearnedStage (R j)) (ρ : ℝ)
    {k l : ℕ} (hkl : k ≤ l) (upper upper' : Bool) (r : ∀ j, R j)
    (xs : List Bool) (hx : xs.length < spent S k) :
    (endpoint S ρ l upper').policy r xs = (endpoint S ρ k upper).policy r xs := by
  have hl := hx.trans_le (spent_mono S hkl)
  change stopAt (spent S l) (reader S r l) xs = stopAt (spent S k) (reader S r k) xs
  rw [stopAt, ite_eq_left hl, stopAt, ite_eq_left hx, reader_compatible S r hkl xs hx]

end ThresholdHC.ArbitraryLawController
