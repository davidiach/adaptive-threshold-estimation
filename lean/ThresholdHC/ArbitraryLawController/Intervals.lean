import ThresholdHC.ArbitraryLawController.Execution
import ThresholdHC.Anytime.IntervalAlgebra

noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace ThresholdHC.ArbitraryLawController
open ThresholdHC.Tier6 ThresholdHC.ArbitraryLawAdaptation ThresholdHC.ObservableSimulation
open ThresholdHC.HardBudget

variable {R : ℕ → Type} [∀ j, MeasurableSpace (R j)]

def observedInterval (S : ∀ j, LearnedStage (R j)) (ρ : ℝ) (k : ℕ)
    (z : (∀ j, R j) × Table) : ℝ × ℝ :=
  let x := populationPath ((endpoint S ρ k false).policy z.1) z.2
  ((endpoint S ρ k false).output (z.1, x), (endpoint S ρ k true).output (z.1, x))

theorem observedInterval_eq (S : ∀ j, LearnedStage (R j)) (ρ : ℝ) (k : ℕ)
    (z : (∀ j, R j) × Table) :
    observedInterval S ρ k z = tableInterval S ρ z.1 z.2 k := by
  dsimp only [observedInterval]
  rw [endpoint_output, show (endpoint S ρ k false).policy = (endpoint S ρ k true).policy from rfl,
    endpoint_output]
  rfl

theorem measurable_observedInterval (S : ∀ j, LearnedStage (R j)) (ρ : ℝ) (k : ℕ) :
    Measurable (observedInterval S ρ k) := by
  let A := endpoint S ρ k false
  have hm : Measurable (fun z : (∀ j, R j) × Table => (z.1, populationPath (A.policy z.1) z.2)) :=
    measurable_fst.prodMk (measurable_seeded_populationPath A.policy
      (fun xs => measurable_to_countable' (A.policy_measurable xs)))
  exact (A.output_measurable.comp hm).prodMk ((endpoint S ρ k true).output_measurable.comp hm)

theorem tableInterval_nested (S : ∀ j, LearnedStage (R j)) (ρ : ℝ)
    (r : ∀ j, R j) (s : Table) {k l : ℕ} (hkl : k ≤ l) :
    (tableInterval S ρ r s k).1 ≤ (tableInterval S ρ r s l).1 ∧
      (tableInterval S ρ r s l).2 ≤ (tableInterval S ρ r s k).2 := by
  have hl : Monotone (fun k => (tableInterval S ρ r s k).1) := by
    apply monotone_nat_of_le_succ
    intro j
    exact le_max_left _ _
  have hu : Antitone (fun k => (tableInterval S ρ r s k).2) := by
    apply antitone_nat_of_succ_le
    intro j
    exact min_le_left _ _
  exact ⟨hl hkl, hu hkl⟩

theorem tableInterval_coverage (S : ∀ j, LearnedStage (R j)) (ρ θ : ℝ)
    (r : ∀ j, R j) (s : Table) (hθ : 0 ≤ θ ∧ θ ≤ ρ)
    (h : ∀ j, ((S j).tableInterval (r j) (s ∘ Nat.pair j)).1 ≤ θ ∧
      θ ≤ ((S j).tableInterval (r j) (s ∘ Nat.pair j)).2) (k : ℕ) :
    (tableInterval S ρ r s k).1 ≤ θ ∧ θ ≤ (tableInterval S ρ r s k).2 := by
  induction k with
  | zero => exact hθ
  | succ j ih => exact ⟨max_le ih.1 (h j).1, le_min ih.2 (h j).2⟩

theorem tableInterval_width (S : ∀ j, LearnedStage (R j)) (ρ : ℝ)
    (r : ∀ j, R j) (s : Table) (j : ℕ) :
    Anytime.halfWidth (tableInterval S ρ r s (j + 1)) ≤
      Anytime.halfWidth ((S j).tableInterval (r j) (s ∘ Nat.pair j)) := by
  unfold Anytime.halfWidth
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply max_le_max_left
  exact sub_le_sub (min_le_right _ _) (le_max_right _ _)

end ThresholdHC.ArbitraryLawController
