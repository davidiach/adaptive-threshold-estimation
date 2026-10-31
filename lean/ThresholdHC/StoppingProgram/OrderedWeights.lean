import ThresholdHC.StoppingProgram.OrderedPrefix
import ThresholdHC.StoppingProgram.RawFlowConstruction

/-! Exact seed-averaged ordered stopping and continuation weights aggregate
to an admissible count flow, without restricting the seed or policy order. -/

noncomputable section
open MeasureTheory
open scoped Classical BigOperators
namespace ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy

theorem integrable_orderedStopIndicator {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsFiniteMeasure ν] (A : StoppedProcedure R E) {n : ℕ} (w : Fin n → Bool) :
    Integrable (orderedStopIndicator A w) ν :=
  Integrable.of_bound (measurable_orderedStopIndicator A w).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun r => by
      rw [Real.norm_of_nonneg (ordered_indicator_bounds A w r).1]
      exact (ordered_indicator_bounds A w r).2.1))

theorem integrable_orderedContinueIndicator {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsFiniteMeasure ν] (A : StoppedProcedure R E) {n : ℕ} (w : Fin n → Bool) :
    Integrable (orderedContinueIndicator A w) ν :=
  Integrable.of_bound (measurable_orderedContinueIndicator A w).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun r => by
      rw [Real.norm_of_nonneg (ordered_indicator_bounds A w r).2.2.1]
      exact (ordered_indicator_bounds A w r).2.2.2))

def orderedStopMass {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) (A : StoppedProcedure R E) {n : ℕ} (w : Fin n → Bool) : ℝ :=
  ∫ r, orderedStopIndicator A w r ∂ν

def orderedContinueMass {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) (A : StoppedProcedure R E) {n : ℕ} (w : Fin n → Bool) : ℝ :=
  ∫ r, orderedContinueIndicator A w r ∂ν

theorem ordered_mass_conservation {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsFiniteMeasure ν] (A : StoppedProcedure R E) {N n : ℕ}
    (hcap : ∀ z, A.stop z ≤ N) (w : Fin n → Bool) (b : Bool) :
    orderedStopMass ν A (Fin.snoc w b)+orderedContinueMass ν A (Fin.snoc w b) = orderedContinueMass ν A w := by
  unfold orderedStopMass orderedContinueMass
  rw [← integral_add (integrable_orderedStopIndicator ν A _) (integrable_orderedContinueIndicator ν A _)]
  exact integral_congr_ae (Filter.Eventually.of_forall (ordered_indicator_conservation A hcap w b))

def headCountMass {n : ℕ} (f : (Fin n → Bool) → ℝ) (k : ℕ) : ℝ :=
  ∑ w, if wordHeads w = k then f w else 0

theorem headCountMass_nonneg {n : ℕ} (f : (Fin n → Bool) → ℝ) (hf : ∀ w, 0 ≤ f w) (k : ℕ) :
    0 ≤ headCountMass f k := by
  apply Finset.sum_nonneg
  intro w _
  split_ifs <;> first | exact hf w | exact le_rfl

theorem headCountMass_outside {n : ℕ} (f : (Fin n → Bool) → ℝ) (k : ℕ) (hk : n < k) :
    headCountMass f k = 0 := by
  apply Finset.sum_eq_zero
  intro w _
  exact ite_eq_right (by have h := wordHeads_le_length w; omega)

theorem headCountMass_add {n : ℕ} (f g : (Fin n → Bool) → ℝ) (k : ℕ) :
    headCountMass (fun w => f w+g w) k = headCountMass f k+headCountMass g k := by
  unfold headCountMass
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w _ => by split_ifs <;> simp)

theorem headCountMass_snoc {n : ℕ} (f : (Fin (n+1) → Bool) → ℝ) (g : (Fin n → Bool) → ℝ)
    (hfg : ∀ w b, f (Fin.snoc w b) = g w) (k : ℕ) :
    headCountMass f k = headCountMass g k+(if 0 < k then headCountMass g (k-1) else 0) := by
  have he := (Fin.snocEquiv (fun _ : Fin (n+1) => Bool)).sum_comp
    (fun w => if wordHeads w = k then f w else 0)
  unfold headCountMass
  rw [← he,Fintype.sum_prod_type,Fintype.sum_bool]
  simp only [Fin.snocEquiv_apply,wordHeads_snoc,hfg,ite_true,Bool.false_eq_true,ite_false,add_zero]
  by_cases hk : 0 < k
  · rw [ite_eq_left hk]
    have htrue : (∑ w : Fin n → Bool, if wordHeads w+1 = k then g w else 0) =
        ∑ w : Fin n → Bool, if wordHeads w = k-1 then g w else 0 := by
      apply Finset.sum_congr rfl
      intro w _
      have heq : wordHeads w+1 = k ↔ wordHeads w = k-1 := by omega
      simp only [heq]
    rw [htrue]
    ring
  · have hk0 : k = 0 := by omega
    simp [hk0]

def orderedCountStop {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) (A : StoppedProcedure R E) (n k : ℕ) : ℝ :=
  headCountMass (orderedStopMass ν A (n := n)) k

def orderedCountContinue {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) (A : StoppedProcedure R E) (n k : ℕ) : ℝ :=
  headCountMass (orderedContinueMass ν A (n := n)) k

def orderedFlow {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) (A : StoppedProcedure R E) (N : ℕ) : Flow N :=
  normalizedRawFlow N (orderedCountStop ν A) (orderedCountContinue ν A)

theorem orderedFlow_cone {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsFiniteMeasure ν] (A : StoppedProcedure R E) (N : ℕ)
    (hcap : ∀ z, A.stop z ≤ N) : FlowCone (orderedFlow ν A N) := by
  apply normalizedRawFlow_cone
  · intro n k
    exact headCountMass_nonneg _ (fun w => integral_nonneg (fun r => (ordered_indicator_bounds A w r).1)) k
  · intro n k
    exact headCountMass_nonneg _ (fun w => integral_nonneg (fun r => (ordered_indicator_bounds A w r).2.2.1)) k
  · exact fun n k hk => headCountMass_outside _ k hk
  · exact fun n k hk => headCountMass_outside _ k hk
  · simp [orderedCountStop,headCountMass,orderedStopMass,orderedStopIndicator]
  · intro k _
    simp [orderedCountContinue,headCountMass,orderedContinueMass,ordered_indicator_terminal A hcap]
  · intro n k _ _
    rw [orderedCountStop,orderedCountContinue,← headCountMass_add,
      headCountMass_snoc _ _ (ordered_mass_conservation ν A hcap) k]
    rfl

end ThresholdHC.StoppingProgram
