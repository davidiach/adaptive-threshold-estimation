import ThresholdHC.Statements

/-!
Shared definitions for the full uniform variance-work argument.
The stopping boundary uses the theory-compatible parameters k₁ = 1/4, k₂ = 1.
This development is separate from the original frozen targets.
-/

noncomputable section

namespace ThresholdHC.Uniform713

open Real MeasureTheory ProbabilityTheory

def cap (l : ℕ) : ℝ := (2 : ℝ) ^ l

def levelProb (l : ℕ) : ℝ := (1 - rLevel) * rLevel ^ l

def threshold (n N : ℝ) : ℝ := Real.sqrt ((1 / 4 + Real.log (N / n)) / n)

def workEnvelope (l : ℕ) (d : ℝ) : ℝ :=
  min (cap l) ((d⁻¹) ^ 2 * (1 + max 0 (Real.log (cap l * d ^ 2))))

def errorPrefactor : ℝ := Real.exp (-2) + (2 / 3) * Real.exp (-(1 / 2 : ℝ))

def increment (z : ℕ → ℝ) : ℕ → ℝ
  | 0 => z 0
  | l + 1 => z (l + 1) - z l

/-- The two one-sided Hoeffding bounds needed by the classifier proof.
This is an intermediate interface, not an assumption of the final model theorem.
-/
structure HasMeanTails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (m : ℕ → Ω → ℝ) (p : ℝ) : Prop where
  measurable : ∀ k, Measurable (m k)
  upper : ∀ k t, 0 ≤ t →
    μ.real {ω | t ≤ m k ω - p} ≤ Real.exp (-2 * cap k * t ^ 2)
  lower : ∀ k t, 0 ≤ t →
    μ.real {ω | t ≤ p - m k ω} ≤ Real.exp (-2 * cap k * t ^ 2)

theorem cap_pos (l : ℕ) : 0 < cap l := by
  unfold cap
  positivity

@[simp] theorem cap_zero : cap 0 = 1 := by simp [cap]

@[simp] theorem cap_succ (l : ℕ) : cap (l + 1) = 2 * cap l := by
  simp [cap, pow_succ, mul_comm]

theorem rLevel_pos : 0 < rLevel := by unfold rLevel; positivity

theorem rLevel_lt_one : rLevel < 1 := by
  unfold rLevel
  exact (inv_lt_one₀ (by positivity)).2 (by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num)

theorem levelProb_pos (l : ℕ) : 0 < levelProb l := by
  exact mul_pos (sub_pos.mpr rLevel_lt_one) (pow_pos rLevel_pos l)

theorem hasSum_levelProb : HasSum levelProb 1 := by
  change HasSum (fun l : ℕ => (1-rLevel) * rLevel ^ l) 1
  have h := (hasSum_geometric_of_lt_one rLevel_pos.le rLevel_lt_one).mul_left (1-rLevel)
  simpa [levelProb, ne_of_gt (sub_pos.mpr rLevel_lt_one)] using h

theorem sum_increment (z : ℕ → ℝ) (L : ℕ) :
    ∑ l ∈ Finset.range (L + 1), increment z l = z L := by
  induction L with
  | zero => simp [increment]
  | succ L ih => rw [Finset.sum_range_succ, ih]; simp [increment]

end ThresholdHC.Uniform713
