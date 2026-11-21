import ThresholdHC.Tier6.AlgorithmModel
import ThresholdHC.EntropyTailExecution.CallMachine
import ThresholdHC.Genie.UniformGapModel

/-! Target statements for the fixed-plan comparison: `docs/RESULTS.md`, section
Practical comparison with a fixed plan (anchor
`practical-comparison-with-a-fixed-plan`), and `docs/SECONDARY_CLAIMS.md`,
item 7 (Fixed-plan comparison and its analytic integral), with the formula of
`EvenlySpread.majority_terms` and `_majority_plan` in
`toolkit/threshold_toolkit/planner.py`.

The source claim: for `n` independent fresh coins and an odd number `m` of flips
per coin, the share of coins with a majority of heads has bias in absolute value
at most the mean misclassification probability `e_m` and variance at most
`1/(4n)`, hence RMS error at most `sqrt(e_m^2+1/(4n))`, uniformly over the sign
laws at a known gap law. For uniformly distributed success rates, with
`a = (m+1)/2`, `e_m = 2 integral_0^(1/2) I_p(a,a) dp = binom(2a,a)/2^(2a+1) =
1/(2a Beta(a,1/2))`.

Formalization choices.
* The odd flip count is `m = 2k+1`, so `a = k+1`.
* `majorityTail k p` is the binomial tail `P(Bin(2k+1,p) ≥ k+1)`. The source
  writes it as the regularized incomplete beta `I_p(k+1,k+1)`; that classical
  identity is not stated here, so the integral is checked in binomial-tail form.
* `majorityMiss k d` is that tail at success rate `1/2 - d`, and `e_m` is its
  integral `meanMajorityMiss μ k` over the gap law. `MajorityMissStatement`
  identifies it with the actual tape probability that the majority vote of a coin
  with gap `d` differs from the coin's sign, for either sign.
* The fixed plan is the checked observable finite-plan controller
  `finitePlanEstimator` with the trivial seed space `Unit`: coins labelled
  `0, ..., n-1`, `2k+1` flips each, output the share of majority-heads coins. It is
  evaluated in the original adaptive experiment `experimentLaw`.
* Every statement except the work statement assumes `0 < n`. At `n = 0` the
  output is `0`, and the mean, bias, mean squared error, RMS and minimax claims
  fail; the variance bound holds trivially and keeps `0 < n` for uniformity.
* The variance bound is stated for `evariance`, which keeps an infinite variance.
  The exact mean is stated as well, and the bias bound follows from it.
* Uniformity over signs is the supremum over all measurable sign laws in
  `maximalRMSRisk`. The exact work `n(2k+1)`, the uniform budget, the mean
  squared error bound and the minimax corollary for `Tier6.minimaxRisk` are added.
* Success rates uniform on `[0,1]` become `Genie.uniformGapLaw`, the uniform law of
  gaps on `(0,1/2]`: a rate `r` has gap `|r - 1/2|`, uniform on `[0,1/2]`, and the
  misclassification probability depends on the gap only.
* `Beta(a,1/2)` is Mathlib's real `ProbabilityTheory.beta`.

Floating-point evaluation in the toolkit and its grid search are not covered. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ThresholdHC.FixedPlan
open ThresholdHC.Tier6 ThresholdHC.Tier2 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.EntropyTailExecution

/-- `P(Bin(2k+1,p) ≥ k+1)`, the binomial-tail form of the source's `I_p(a,a)`
with `a = k+1`. -/
def majorityTail (k : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico (k+1) (2*k+2), ((2*k+1).choose j : ℝ) * p^j * (1-p)^(2*k+1-j)

/-- Misclassification probability of the majority of `2k+1` flips of a coin with
gap `d`, for either sign. -/
def majorityMiss (k : ℕ) (d : Gap) : ℝ := majorityTail k (1/2 - (d : ℝ))

/-- The mean misclassification probability `e_m` at the gap law `μ`, `m = 2k+1`. -/
def meanMajorityMiss (μ : Measure Gap) (k : ℕ) : ℝ := ∫ d, majorityMiss k d ∂μ

/-- Majority indicator of a coin's first `2k+1` flips. -/
def majorityVote (k : ℕ) (ω : ℕ → Bool) : ℝ :=
  if k+1 ≤ wordHeads (tapePrefix (2*k+1) ω) then 1 else 0

/-- One coin of the fixed plan: `2k+1` flips, contributing its majority indicator
divided by `n`. -/
def majorityCall (k n : ℕ) : FiniteCall where
  cost := fun _ => 2*k+1
  value := fun ω => (n : ℝ)⁻¹ * majorityVote k ω
  measurable_cost := measurable_const
  measurable_value := measurable_const.mul
    ((measurable_of_countable (fun w : Fin (2*k+1) → Bool =>
      if k+1 ≤ wordHeads w then (1 : ℝ) else 0)).comp (measurable_prefix (2*k+1)))
  positive := fun _ => by omega
  prefix_ext := fun ω ω' h => by
    refine ⟨rfl, ?_⟩
    unfold majorityVote
    rw [h]

/-- The fixed plan: `n` fresh coins (labels `0, ..., n-1`), `2k+1` flips each;
output the share of coins with a majority of heads. -/
def majorityEstimator (k n : ℕ) : AdaptiveEstimator Unit :=
  finitePlanEstimator (Measure.dirac ()) (fun _ => majorityCall k n) (fun _ => List.range n)

/-- The expected work of the plan is exactly `n(2k+1)`, for every gap law and
sign law. -/
def MajorityWorkStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k n : ℕ),
    expectedWork μ (majorityEstimator k n) q = ((n*(2*k+1) : ℕ) : ℝ≥0∞)

/-- `majorityMiss k d` is the probability that the majority vote of a coin with
gap `d` differs from the coin's sign, for either sign. -/
def MajorityMissStatement : Prop :=
  ∀ (k : ℕ) (d : Gap) (s : Bool),
    (tapeMeasure (gapParameter s d)).real {ω | majorityVote k ω ≠ bit s} = majorityMiss k d

/-- Exact mean of the plan's output. -/
def MajorityMeanStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k n : ℕ), 0 < n →
    (∫ z, populationOutput (majorityEstimator k n) z ∂experimentLaw μ (majorityEstimator k n) q) =
      ∫ d, q.val d * (1 - majorityMiss k d) + (1 - q.val d) * majorityMiss k d ∂μ

/-- The bias is at most the mean misclassification probability `e_m`. -/
def MajorityBiasStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k n : ℕ), 0 < n →
    |(∫ z, populationOutput (majorityEstimator k n) z ∂experimentLaw μ (majorityEstimator k n) q)
      - signMean μ q.val| ≤ meanMajorityMiss μ k

/-- The variance is at most `1/(4n)`. -/
def MajorityVarianceStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k n : ℕ), 0 < n →
    evariance (populationOutput (majorityEstimator k n)) (experimentLaw μ (majorityEstimator k n) q)
      ≤ ENNReal.ofReal (1 / (4 * (n : ℝ)))

/-- The mean squared error is at most `e_m^2 + 1/(4n)`. -/
def MajorityMSEStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k n : ℕ), 0 < n →
    squaredRisk (experimentLaw μ (majorityEstimator k n) q) (populationOutput (majorityEstimator k n))
      (signMean μ q.val) ≤ ENNReal.ofReal (meanMajorityMiss μ k ^ 2 + 1 / (4 * (n : ℝ)))

/-- Uniformly over sign laws, the plan has budget `n(2k+1)` and RMS error at most
`sqrt(e_m^2 + 1/(4n))`. -/
def MajorityRMSStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (k n : ℕ), 0 < n →
    UniformBudget μ (majorityEstimator k n) ((n*(2*k+1) : ℕ) : ℝ) ∧
    maximalRMSRisk μ (majorityEstimator k n) ≤
      ENNReal.ofReal (Real.sqrt (meanMajorityMiss μ k ^ 2 + 1 / (4 * (n : ℝ))))

/-- Minimax corollary: at every budget `B ≥ n(2k+1)`. -/
def MajorityMinimaxStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (k n : ℕ) (B : ℝ), 0 < n →
    ((n*(2*k+1) : ℕ) : ℝ) ≤ B →
    Tier6.minimaxRisk μ B ≤ ENNReal.ofReal (Real.sqrt (meanMajorityMiss μ k ^ 2 + 1 / (4 * (n : ℝ))))

/-- `2 integral_0^(1/2) P(Bin(2a-1,p) ≥ a) dp = binom(2a,a)/2^(2a+1)` with
`a = k+1`; the source writes the integrand as `I_p(a,a)`. -/
def UniformTailIntegralStatement : Prop :=
  ∀ k : ℕ, 2 * (∫ p in (0:ℝ)..(1/2), majorityTail k p) =
    ((2*(k+1)).choose (k+1) : ℝ) / 2 ^ (2*(k+1)+1)

/-- At the uniform gap law, `e_m = binom(2a,a)/2^(2a+1)` with `a = k+1`. -/
def UniformMeanMissStatement : Prop :=
  ∀ k : ℕ, meanMajorityMiss Genie.uniformGapLaw k = ((2*(k+1)).choose (k+1) : ℝ) / 2 ^ (2*(k+1)+1)

/-- `binom(2a,a)/2^(2a+1) = 1/(2a Beta(a,1/2))` with Mathlib's real beta, `a = k+1`. -/
def UniformBetaStatement : Prop :=
  ∀ k : ℕ, ((2*(k+1)).choose (k+1) : ℝ) / 2 ^ (2*(k+1)+1) =
    1 / (2 * ((k : ℝ)+1) * ProbabilityTheory.beta ((k : ℝ)+1) (1/2))

end ThresholdHC.FixedPlan
