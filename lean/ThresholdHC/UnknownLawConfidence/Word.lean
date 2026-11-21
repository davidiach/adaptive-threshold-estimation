import ThresholdHC.UnknownLawConfidence.Counts
import ThresholdHC.LawAdaptation.Execution

/-! The stage word as a function of the coin table.

The stage interval sees the word bought by the stage reader on the
continuation coins. Item `i` reads the coin `itemCoin i = Nat.pair 1 (Nat.pair i 0)`
of the stage-local table, and its observed head fraction is the head count of
the first `m` flips of that tape over `m`. The positive and negative sample
fractions are therefore prefix means of indicators of independent tapes. No
probability enters here. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace ThresholdHC.UnknownLawConfidence
open ThresholdHC.HardBudget ThresholdHC.ArbitraryLawAdaptation ThresholdHC.Uniform713

/-- The coin of item `i` in a stage-local table. -/
def itemCoin (i : ℕ) : ℕ := Nat.pair 1 (Nat.pair i 0)

theorem itemCoin_injective : Function.Injective itemCoin := by
  intro a b h
  have h1 := (Nat.pair_eq_pair.mp h).2
  exact (Nat.pair_eq_pair.mp h1).1

/-- The word bought by stage `j` from a stage-local table. -/
def stageWord (j : ℕ) (t : Table) : List Bool :=
  (readBlock (itemCount j * flipCount j) (stageReader j) (t ∘ Nat.pair 1)).1

theorem stage_tableInterval (δ : ℝ) (j : ℕ) (t : Table) :
    (stage δ j).tableInterval () t = stageInterval δ j (stageWord j t) := rfl

theorem count_ofFn (m : ℕ) (ω : ℕ → Bool) :
    (List.ofFn (fun k : Fin m => ω k.val)).count true = tailHeads m ω := by
  induction m with
  | zero => simp [tailHeads]
  | succ m ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.count_append, tailHeads_succ]
    simp only [Fin.val_castSucc, Fin.val_last] at *
    rw [ih]
    cases ω m <;> simp

/-- The observed head fraction of a tape after `m` flips. -/
def tapeFraction (j : ℕ) (ω : ℕ → Bool) : ℝ := (tailHeads (flipCount j) ω : ℝ) / flipCount j

theorem itemFraction_stageWord (j : ℕ) {i : ℕ} (hi : i < itemCount j) (t : Table) :
    itemFraction j i (stageWord j t) = tapeFraction j (t (itemCoin i)) := by
  have h := (seqReader_readBlock (fun _ => flipCount j) (fun _ _ => 0) (t ∘ Nat.pair 1)
    (itemCount j)).1 i hi
  rw [seqOffset_const] at h
  unfold itemFraction tapeFraction
  change ((seqWord (fun _ => flipCount j) i (readBlock (itemCount j * flipCount j)
    (seqReader (fun _ => flipCount j) (fun _ _ => 0) (itemCount j)) (t ∘ Nat.pair 1)).1).count
      true : ℝ) / flipCount j = _
  rw [h, ThresholdHC.LawAdaptation.readBlock_constant, count_ofFn]
  rfl

/-- Tapes declared positive. -/
def posSet (j : ℕ) : Set (ℕ → Bool) := {ω | 1 / 2 + radius j < tapeFraction j ω}

/-- Tapes declared negative. -/
def negSet (j : ℕ) : Set (ℕ → Bool) := {ω | tapeFraction j ω < 1 / 2 - radius j}

/-- Unresolved tapes. -/
def zeroSet (j : ℕ) : Set (ℕ → Bool) := (posSet j ∪ negSet j)ᶜ

theorem measurable_tapeFraction (j : ℕ) : Measurable (tapeFraction j) :=
  (measurable_of_countable (fun h : ℕ => (h : ℝ) / flipCount j)).comp
    (measurable_tailHeads (flipCount j))

theorem measurableSet_posSet (j : ℕ) : MeasurableSet (posSet j) :=
  measurableSet_lt measurable_const (measurable_tapeFraction j)

theorem measurableSet_negSet (j : ℕ) : MeasurableSet (negSet j) :=
  measurableSet_lt (measurable_tapeFraction j) measurable_const

theorem measurableSet_zeroSet (j : ℕ) : MeasurableSet (zeroSet j) :=
  ((measurableSet_posSet j).union (measurableSet_negSet j)).compl

theorem posSet_negSet_disjoint (j : ℕ) : Disjoint (posSet j) (negSet j) := by
  rw [Set.disjoint_left]
  intro ω hp hn
  have hr := radius_nonneg j
  change 1 / 2 + radius j < tapeFraction j ω at hp
  change tapeFraction j ω < 1 / 2 - radius j at hn
  linarith

/-- The indicator of an outcome of item `i` in a stage-local table. -/
def outcome (A : Set (ℕ → Bool)) (i : ℕ) (t : Table) : ℝ :=
  A.indicator (fun _ => (1 : ℝ)) (t (itemCoin i))

theorem measurable_outcome {A : Set (ℕ → Bool)} (hA : MeasurableSet A) (i : ℕ) :
    Measurable (outcome A i) :=
  (measurable_const.indicator hA).comp (measurable_pi_apply (itemCoin i))

theorem outcome_mem_Icc (A : Set (ℕ → Bool)) (i : ℕ) (t : Table) :
    outcome A i t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold outcome
  by_cases h : t (itemCoin i) ∈ A <;> simp [h]

open scoped Classical in
theorem sum_outcome (A : Set (ℕ → Bool)) (n : ℕ) (t : Table) :
    ∑ i ∈ Finset.range n, outcome A i t =
      (((Finset.range n).filter (fun i => t (itemCoin i) ∈ A)).card : ℝ) := by
  unfold outcome
  simp only [Set.indicator_apply]
  exact Finset.sum_boole _ _

open scoped Classical in
theorem positiveCount_eq (j : ℕ) (t : Table) :
    (positiveCount j (stageWord j t) : ℝ) / itemCount j =
      prefixMean (outcome (posSet j)) (itemCount j) t := by
  unfold prefixMean
  rw [sum_outcome]
  congr 2
  unfold positiveCount
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [itemFraction_stageWord j (Finset.mem_range.mp hi)]
  rfl

open scoped Classical in
theorem negativeCount_eq (j : ℕ) (t : Table) :
    (negativeCount j (stageWord j t) : ℝ) / itemCount j =
      prefixMean (outcome (negSet j)) (itemCount j) t := by
  unfold prefixMean
  rw [sum_outcome]
  congr 2
  unfold negativeCount
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [itemFraction_stageWord j (Finset.mem_range.mp hi)]
  rfl

/-- The three sample fractions sum to one. -/
theorem prefixMean_outcome_sum (j : ℕ) (t : Table) :
    prefixMean (outcome (posSet j)) (itemCount j) t +
      prefixMean (outcome (negSet j)) (itemCount j) t +
      prefixMean (outcome (zeroSet j)) (itemCount j) t = 1 := by
  have hpt : ∀ i, outcome (posSet j) i t + outcome (negSet j) i t +
      outcome (zeroSet j) i t = 1 := by
    intro i
    unfold outcome
    have hd : t (itemCoin i) ∈ posSet j → t (itemCoin i) ∉ negSet j :=
      fun h => Set.disjoint_left.mp (posSet_negSet_disjoint j) h
    by_cases hp : t (itemCoin i) ∈ posSet j
    · have hn := hd hp
      simp [zeroSet, hp, hn]
    · by_cases hn : t (itemCoin i) ∈ negSet j
      · simp [zeroSet, hp, hn]
      · simp [zeroSet, hp, hn]
  have hn : (itemCount j : ℝ) ≠ 0 := by exact_mod_cast (itemCount_pos j).ne'
  unfold prefixMean
  rw [← add_div, ← add_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  simp only [hpt, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact div_self hn

end ThresholdHC.UnknownLawConfidence
