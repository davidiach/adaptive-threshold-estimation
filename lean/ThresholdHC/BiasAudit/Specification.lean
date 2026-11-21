import ThresholdHC.Statements2

/-! Target statements for the bias audit of the constant search,
`proposals/constants/BIAS_AUDIT.md`: the section on the finite-grid winner violating
the uniform bias theorem (lines 49-69) and the section on a smaller threshold that
preserves the v4 bias theorem (lines 6-41). The first is also cited in
`paper/v6/verification.tex` (paragraph on numerical evidence and its limits, lines
538-541: the grid-winning logarithmic threshold coefficient `1/2` fails the uniform
error envelope at an explicit large cap).

Here the source's `e_N` is the frozen `errProbK k1 k2 L d S` of `Statements2.lean`: the
misclassification probability of the cap-`2^L` classifier `classifyK`, with early-stop
threshold `thrK k1 k2 n N = sqrt((k1 + k2 log(N/n))/n)`, on an iid Bernoulli stream with
success probability `coinP d S = 1/2 ± d`. This is the model of the frozen evaluator
`constants/evaluator.py`: early stops only at prefixes `n < N`, a strict comparison with
the threshold, and a tie at the cap counted as negative. The v4 envelope is
`min(1, (N d²)^{-2})` with `N = 2^L`; at `k1 = k2 = 1` it is the frozen target
`Targets.lemma6_error`. The proofs are in `Counterexample.lean` and
`SmallerThreshold.lean`. -/
noncomputable section
namespace ThresholdHC.BiasAudit
open ThresholdHC

/-- BIAS_AUDIT.md:49-69. For the grid winner `(k₁,k₂) = (1/4,1/2)`, positive sign,
`d = 1/10` and cap `N = 2^97`: `e_N ≥ (2/5)^128`, and this exceeds `2907` times the v4
envelope `min(1,(N d²)^{-2})` (the exact ratio is `2^318/5^132 ≈ 2907.35`). -/
def GridWinnerCounterexampleStatement : Prop :=
  (2/5 : ℝ) ^ 128 ≤ errProbK (1/4) (1/2) 97 (1/10) true ∧
    2907 * min 1 ((((2 : ℝ) ^ 97 * (1/10) ^ 2)⁻¹) ^ 2) < (2/5 : ℝ) ^ 128

/-- BIAS_AUDIT.md:49-69, read against the v4 Lemma 6 envelope: the grid winner
`(k₁,k₂) = (1/4,1/2)` does not satisfy the form of `Targets.lemma6_error`. -/
def GridWinnerFailsEnvelopeStatement : Prop :=
  ¬ ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    errProbK (1/4) (1/2) L d S ≤ min 1 ((((2 : ℝ) ^ L * d ^ 2)⁻¹) ^ 2)

/-- BIAS_AUDIT.md:6-41. For `k₁ ≥ 0`, `k₂ ≥ 1`, either sign, every cap `N = 2^L` and
`0 < d ≤ 1/2`, with `x = N d²`: `e_N ≤ exp(-2x) + (2/3) exp(-2k₁) x^{-2}` and
`e_N ≤ min(1, x^{-2})`. At `k₁ = k₂ = 1` the second conjunct is `Targets.lemma6_error`. -/
def SmallerThresholdErrorStatement : Prop :=
  ∀ (k₁ k₂ : ℝ), 0 ≤ k₁ → 1 ≤ k₂ → ∀ (L : ℕ) (d : ℝ) (S : Bool), 0 < d → d ≤ 1/2 →
    errProbK k₁ k₂ L d S ≤
        Real.exp (-2 * ((2 : ℝ) ^ L * d ^ 2)) +
          2/3 * Real.exp (-2 * k₁) * (((2 : ℝ) ^ L * d ^ 2)⁻¹) ^ 2 ∧
      errProbK k₁ k₂ L d S ≤ min 1 ((((2 : ℝ) ^ L * d ^ 2)⁻¹) ^ 2)

end ThresholdHC.BiasAudit
