
import ThresholdHC.Proofs.DyadicSummable
noncomputable section
set_option linter.unusedVariables false
open ThresholdHC.Proofs

example : ∀ {b : ℝ} (hb : 0 < b) (m : ℕ),
    ∑ k ∈ Finset.range m, (2:ℝ)^k * Real.exp (-(b*2^k)) ≤ 2 / b := @dyadic_partial_v1
example : ∀ {b : ℝ} (hb : 0 < b),
    ∃ s, HasSum (fun k : ℕ => (2:ℝ)^k * Real.exp (-(b*2^k))) s ∧ s ≤ 2 / b := @dyadic_hasSum_v1
example : ∀ {b : ℝ} (hb : 0 < b) (k : ℕ),
    ((2:ℝ)^k)^2 * Real.exp (-(b*2^k)) ≤ (2 / b) * ((2:ℝ)^k * Real.exp (-((b/2)*2^k))) :=
  @dyadic_term_v2
example : ∀ {b : ℝ} (hb : 0 < b) (m : ℕ),
    ∑ k ∈ Finset.range m, ((2:ℝ)^k)^2 * Real.exp (-(b*2^k)) ≤ 8 / b^2 := @dyadic_partial_v2
example : ∀ {b : ℝ} (hb : 0 < b),
    ∃ s, HasSum (fun k : ℕ => ((2:ℝ)^k)^2 * Real.exp (-(b*2^k))) s ∧ s ≤ 8 / (3 * b^2) :=
  @dyadic_hasSum_v2
-- The frozen targets the two sums bound, unchanged.
example : ThresholdHC.Targets.dyadic_sum_v1 ↔
    ∀ b : ℝ, 0 < b → ∑' k : ℕ, (2 : ℝ) ^ k * Real.exp (-(b * 2 ^ k)) ≤ 2 / b := Iff.rfl
example : ThresholdHC.Targets.dyadic_sum_v2 ↔
    ∀ b : ℝ, 0 < b → ∑' k : ℕ, ((2 : ℝ) ^ k) ^ 2 * Real.exp (-(b * 2 ^ k)) ≤ 8 / (3 * b ^ 2) :=
  Iff.rfl
#print axioms ThresholdHC.Proofs.dyadic_hasSum_v1
#print axioms ThresholdHC.Proofs.dyadic_hasSum_v2
#print axioms ThresholdHC.Proofs.dyadic_partial_v1
#print axioms ThresholdHC.Proofs.dyadic_partial_v2
#print axioms ThresholdHC.Proofs.dyadic_term_v2
