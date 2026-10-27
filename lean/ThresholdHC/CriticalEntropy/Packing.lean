import Mathlib

/-!
The entropy-packing implication used in BC4 of the critical-law paper.

This module proves an event-packing inequality and its analytic consequence.
It does not assume that any particular Bernoulli test supplies the events.
Constructing those events with the required mass and overlap bounds is a
separate statistical obligation, not a conclusion of these theorems.
-/

noncomputable section
open MeasureTheory Real

namespace ThresholdHC.CriticalEntropy

/-- Integrating a pointwise overlap bound controls the sum of event masses. -/
theorem sum_event_mass_le_overlap {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι)
    (A : ι → Set Ω) (hA : ∀ i ∈ s, MeasurableSet (A i))
    (overlap : ℝ)
    (hcover : ∀ ω, (∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ)) ω) ≤ overlap) :
    (∑ i ∈ s, μ.real (A i)) ≤ overlap := by
  classical
  have hi (i : ι) (his : i ∈ s) :
      Integrable ((A i).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator (hA i his)
  have h := integral_mono (integrable_finsetSum s hi) (integrable_const overlap) hcover
  rw [integral_finsetSum s hi] at h
  have heq : (∑ i ∈ s, ∫ ω, (A i).indicator (fun _ => (1 : ℝ)) ω ∂μ) =
      ∑ i ∈ s, μ.real (A i) := by
    apply Finset.sum_congr rfl
    intro i his
    simpa using integral_indicator_const (1 : ℝ) (hA i his) (μ := μ)
  rw [heq] at h
  simpa using h

/-- A common lower bound on event probabilities, combined with a common
pointwise overlap bound, gives a finite packing inequality. -/
theorem event_packing {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι)
    (A : ι → Set Ω) (hA : ∀ i ∈ s, MeasurableSet (A i))
    (mass overlap : ℝ) (hmass : ∀ i ∈ s, mass ≤ μ.real (A i))
    (hcover : ∀ ω, (∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ)) ω) ≤ overlap) :
    (s.card : ℝ) * mass ≤ overlap := by
  calc
    _ = ∑ _i ∈ s, mass := by simp
    _ ≤ ∑ i ∈ s, μ.real (A i) := Finset.sum_le_sum hmass
    _ ≤ overlap := sum_event_mass_le_overlap μ s A hA overlap hcover

/-- A convenient analytic upper bound for the multiplicity in BC4. -/
theorem overlap_bound (x c : ℝ) (hx : 32 ≤ x) (hc : 0 ≤ c)
    (hsmall : c ≤ x / 512) :
    1 + log (1024 * (16 * c + 2)) / log 4 ≤ 12 + x / 64 := by
  have hx0 : 0 ≤ x := by linarith
  have hcarg : 0 < 1024 * (16 * c + 2) := by positivity
  have hlog0 : 0 ≤ log (1024 * (16 * c + 2)) :=
    log_nonneg (by nlinarith)
  have hlog4 : 1 ≤ log (4 : ℝ) := by
    have he : log (4 : ℝ) = 2 * log 2 := by
      convert log_pow (2 : ℝ) 2 using 1; norm_num
    rw [he]
    linarith [log_two_gt_d9]
  have hdiv : log (1024 * (16 * c + 2)) / log 4 ≤
      log (1024 * (16 * c + 2)) :=
    (div_le_iff₀ (by linarith : 0 < log (4 : ℝ))).2
      (le_mul_of_one_le_right hlog0 hlog4)
  have hmono : log (1024 * (16 * c + 2)) ≤ log (2048 * (1 + x / 64)) :=
    log_le_log hcarg (by nlinarith)
  have h2048 : log (2048 : ℝ) = 11 * log 2 := by
    convert log_pow (2 : ℝ) 11 using 1; norm_num
  rw [log_mul (by norm_num : (2048 : ℝ) ≠ 0)
    (ne_of_gt (by positivity : 0 < 1 + x / 64)), h2048] at hmono
  have hlog := log_le_sub_one_of_pos (by positivity : 0 < 1 + x / 64)
  have hlog2 : log (2 : ℝ) ≤ 1 := by linarith [log_two_lt_d9]
  linarith

/-- The analytic contradiction in BC4, with the paper's constant 1/512.
The hypothesis is a packing inequality; no sign-testing theorem is assumed. -/
theorem entropy_of_packing (x c : ℝ) (hx : 32 ≤ x) (hc : 0 ≤ c)
    (hpack : (1 / 2 : ℝ) * exp (x - 128 * c - 8) ≤
      1 + log (1024 * (16 * c + 2)) / log 4) :
    x / 512 ≤ c := by
  by_contra hn
  have hsmall : c < x / 512 := lt_of_not_ge hn
  have hx0 : 0 ≤ x := by linarith
  have hexp : exp (x / 2) ≤ exp (x - 128 * c - 8) :=
    exp_le_exp.mpr (by linarith)
  have hquad := quadratic_le_exp_of_nonneg (show 0 ≤ x / 2 by positivity)
  have hover := overlap_bound x c hx hc hsmall.le
  have hprod : 0 ≤ x * (x - 32) := mul_nonneg hx0 (by linarith)
  nlinarith

/-- BC4 expressed with the number of gaps rather than its logarithm. -/
theorem entropy_of_gap_count (K c : ℝ) (hK : 0 < K) (hlarge : 32 ≤ log K)
    (hc : 0 ≤ c)
    (hpack : (K / 2) * exp (-128 * c - 8) ≤
      1 + log (1024 * (16 * c + 2)) / log 4) :
    log K / 512 ≤ c := by
  apply entropy_of_packing (log K) c hlarge hc
  have he : exp (log K - 128 * c - 8) = K * exp (-128 * c - 8) := by
    rw [show log K - 128 * c - 8 = log K + (-128 * c - 8) by ring,
      exp_add, exp_log hK]
  rw [he]
  nlinarith [exp_pos (-128 * c - 8)]

end ThresholdHC.CriticalEntropy
