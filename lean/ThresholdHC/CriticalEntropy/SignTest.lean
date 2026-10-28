import ThresholdHC.CriticalEntropy.EventInformation
import Mathlib

/-!
Observable single-coin sign tests. The stopping time is an extended natural
number of actual flips. Its terminal decision by time `n` is determined by
the independent seed and the first `n` flips. Neither the test nor its seed
law is indexed by the coin parameter. Infinite work is retained.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace ThresholdHC.CriticalEntropy

structure SignTest (R : Type) [MeasurableSpace R] where
  stop : R × (ℕ → Bool) → ℕ∞
  output : R × (ℕ → Bool) → Bool
  measurable_stop : Measurable stop
  measurable_output : Measurable output
  prefixEvent : (n : ℕ) → Bool → Set (R × (Fin n → Bool))
  measurable_prefixEvent : ∀ n b, MeasurableSet (prefixEvent n b)
  observable : ∀ n b z,
    (z.1, Tier2.tapePrefix n z.2) ∈ prefixEvent n b ↔ stop z ≤ n ∧ output z = b

def signTestWork {R : Type} [MeasurableSpace R] (A : SignTest R)
    (z : R × (ℕ → Bool)) : ℝ≥0∞ := A.stop z

def expectedSignTestWork {R : Type} [MeasurableSpace R]
    (ν : Measure R) (p : unitInterval) (A : SignTest R) : ℝ≥0∞ :=
  ∫⁻ z, signTestWork A z ∂ν.prod (Tier2.tapeMeasure p)

def signTestWindow {R : Type} [MeasurableSpace R] (A : SignTest R) (n u : ℕ) :
    Set (R × (ℕ → Bool)) :=
  {z | A.output z = false ∧ (n : ℕ∞) < A.stop z ∧ A.stop z ≤ u}

theorem measurable_signTestWork {R : Type} [MeasurableSpace R] (A : SignTest R) :
    Measurable (signTestWork A) :=
  (measurable_of_countable ENat.toENNReal).comp A.measurable_stop

theorem measurable_signTestWindow {R : Type} [MeasurableSpace R]
    (A : SignTest R) (n u : ℕ) : MeasurableSet (signTestWindow A n u) := by
  exact (measurableSet_eq_fun A.measurable_output measurable_const).inter
    ((A.measurable_stop (Set.to_countable {t : ℕ∞ | (n : ℕ∞) < t}).measurableSet).inter
      (A.measurable_stop (Set.to_countable {t : ℕ∞ | t ≤ (u : ℕ∞)}).measurableSet))

/-- A finite-prefix terminal event has exactly its probability in the actual
infinite experiment. This also covers stopping without any flips. -/
theorem signTest_prefix_probability {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : SignTest R) (n : ℕ) (b : Bool) :
    (ν.prod (Tier2.finiteMeasure p n)).real (A.prefixEvent n b) =
      (ν.prod (Tier2.tapeMeasure p)).real {z | A.stop z ≤ n ∧ A.output z = b} := by
  rw [← seeded_tape_prefix_map ν p n,
    map_measureReal_apply (measurable_id.prodMap (Tier2.measurable_prefix n))
      (A.measurable_prefixEvent n b)]
  congr 1
  ext z
  exact A.observable n b z

/-- Finite expected work forces termination under the same law. No other
parameter's termination is inferred from this statement. -/
theorem signTest_terminates {R : Type} [MeasurableSpace R]
    (ν : Measure R) (p : unitInterval) (A : SignTest R)
    (hfinite : expectedSignTestWork ν p A ≠ ∞) :
    (ν.prod (Tier2.tapeMeasure p)) {z | A.stop z = ⊤} = 0 := by
  have h := measure_eq_top_of_lintegral_ne_top
    (measurable_signTestWork A).aemeasurable hfinite
  simpa only [signTestWork, ENat.toENNReal_eq_top] using h

/-- Markov's bound for the actual flip count, expressed using finite real
expected work only after proving it is finite. -/
theorem signTest_late_probability {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval)
    (A : SignTest R) (u : ℕ) (hfinite : expectedSignTestWork ν p A ≠ ∞) :
    (u : ℝ) * (ν.prod (Tier2.tapeMeasure p)).real {z | (u : ℕ∞) < A.stop z} ≤
      (expectedSignTestWork ν p A).toReal := by
  have hset : {z | (u : ℕ∞) < A.stop z} ⊆ {z | (u : ℝ≥0∞) ≤ signTestWork A z} := by
    intro z hz
    exact ENat.natCast_le_toENNReal.mpr hz.le
  have h := (mul_le_mul (le_refl (u : ℝ≥0∞)) (measure_mono hset) bot_le bot_le).trans
    (mul_meas_ge_le_lintegral (μ := ν.prod (Tier2.tapeMeasure p))
      (measurable_signTestWork A) (u : ℝ≥0∞))
  have hr := ENNReal.toReal_mono hfinite h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, measureReal_def,
    expectedSignTestWork] using hr

/-- A correct negative decision, excluding early decisions and late work,
belongs to the stopping window. This is a probability-space union bound. -/
theorem signTest_window_probability {R : Type} [MeasurableSpace R]
    (P : Measure (R × (ℕ → Bool))) [IsProbabilityMeasure P]
    (A : SignTest R) (n u : ℕ)
    (herror : P.real {z | A.output z = true} ≤ 1/10)
    (hearly : P.real {z | A.stop z ≤ n ∧ A.output z = false} ≤ 9/40)
    (hlate : P.real {z | (u : ℕ∞) < A.stop z} ≤ 1/4) :
    (17/40 : ℝ) ≤ P.real (signTestWindow A n u) := by
  have hcover : Set.univ ⊆ signTestWindow A n u ∪
      ({z | A.output z = true} ∪
        ({z | A.stop z ≤ n ∧ A.output z = false} ∪ {z | (u : ℕ∞) < A.stop z})) := by
    intro z hz
    cases hout : A.output z
    · by_cases hn : A.stop z ≤ n
      · exact Or.inr (Or.inr (Or.inl ⟨hn, hout⟩))
      · by_cases hu : A.stop z ≤ u
        · exact Or.inl ⟨hout, lt_of_not_ge hn, hu⟩
        · exact Or.inr (Or.inr (Or.inr (lt_of_not_ge hu)))
    · exact Or.inr (Or.inl hout)
  have h1 := measureReal_mono (μ := P) hcover
  have h2 := measureReal_union_le (μ := P) (signTestWindow A n u)
    ({z | A.output z = true} ∪
      ({z | A.stop z ≤ n ∧ A.output z = false} ∪ {z | (u : ℕ∞) < A.stop z}))
  have h3 := measureReal_union_le (μ := P) {z | A.output z = true}
    ({z | A.stop z ≤ n ∧ A.output z = false} ∪ {z | (u : ℕ∞) < A.stop z})
  have h4 := measureReal_union_le (μ := P)
    {z | A.stop z ≤ n ∧ A.output z = false} {z | (u : ℕ∞) < A.stop z}
  rw [probReal_univ] at h1
  linarith

end ThresholdHC.CriticalEntropy
