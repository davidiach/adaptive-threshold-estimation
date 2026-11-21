import ThresholdHC.Tier6.AlgorithmModel

/-! Target statements for charging a fee per created coin.

Source: `paper/v6/core.tex`, section `Model, notation, and main results`
(label `sec:model`), the model paragraph that begins: An algorithm has an
independent random seed, creates finitely many coins before each observation.
It ends with the two sentences: Every coin actually created by the upper
algorithm receives at least one observation. Charging a fixed additional amount
per new outer draw therefore changes its cost by at most a constant factor.
The same paragraph is in `paper/v5/core.tex` and `paper/paper.tex`.

Reading of the source in the Lean model (`Tier6`):

* There is no coin-creation action separate from selection. The gap array
  `u.2` of `PopulationSeed` is drawn iid in advance, and an entry that is never
  selected has no effect on the experiment. A coin is created when its label is
  first selected, so a new outer draw is a new distinct selected label.
  `createdLabels pol x n` is the set of labels the policy selects at the steps
  before `n` along the tape `x`, and `totalCreated` is the supremum of its
  cardinality over `n`, in `[0, ∞]`.
* Distinct labels, not the largest label, are counted. The audited upper
  witness (`UpperScale.scaledFamily`) encodes its labels with `Nat.pair`
  (`BlindUpper.controlLabel`), so the largest label used can far exceed the
  number of observations; counting pre-drawn gaps up to the largest label would
  make the fee factor `1 + c` fail for that witness.
* Coins created but never observed, which the paper's model allows, cannot be
  represented: in Lean a coin exists only once it is selected, and a selection
  is an observation almost surely.

Targets:

* `CreatedObservedStatement`: the first source sentence, for every adaptive
  estimator (the source states it only for the upper algorithm). Almost surely,
  every created label was selected at an earlier step that received an
  observation, and the number of created coins is at most the work. Its first
  conjunct holds by construction of the Lean model; the counting inequality is
  the content used below.
* `ChargedWorkStatement`: the second source sentence with the explicit factor
  `1 + c`. With a fee `c ≥ 0` per created coin on top of one per observation,
  the expected cost lies between the expected work and `1 + c` times it.
* `ChargedBlindUpperStatement`: one budget-indexed family, chosen before the
  gap law, keeps the uniform budget `B`, the charged budget `(1 + c)*B` for
  every fee `c ≥ 0`, and RMS risk at most `12` times the modulus. The proof
  uses the audited distribution-blind family `UpperScale.scaledFamily`.
* `ChargedMinimaxStatement` and `ChargedRateStatement` go beyond the source:
  the charged minimax risk lies between `minimaxRisk μ B` and
  `minimaxRisk μ (B/(1+c))`, and for `B ≥ 1 + c` it lies between
  `ω(B^{-1/2})/6` and `12*sqrt(1+c)*ω(B^{-1/2})`. The constant
  `12*sqrt(1+c)` is one valid choice, not a sharp one, and the rate is stated
  only for `B ≥ 1 + c`, where the upper bound of `UpperScale` applies at budget
  `B/(1+c)`.

The source's remark that finite internal computation between observations is
implicit has no target: the Lean class has no computability constraint, and
the upper witness is noncomputable with real-valued seeds. -/
noncomputable section
namespace ThresholdHC.CreationCharge
open MeasureTheory ThresholdHC.Tier3 ThresholdHC.Tier6
open scoped ENNReal

/-- Labels the policy selects at the steps before `n` along the tape `x`; the first
selection of a label creates its coin (one fresh gap draw `u.2 i`). -/
def createdLabels (pol : List Bool → Option ℕ) (x : ProcessTape) (n : ℕ) : Finset ℕ :=
  Finset.univ.biUnion (fun k : Fin n => (pol (processHistory x k)).toFinset)

/-- Number of coins created along the whole tape, in `[0, ∞]`. -/
def totalCreated (pol : List Bool → Option ℕ) (x : ProcessTape) : ℝ≥0∞ :=
  ⨆ n : ℕ, ((createdLabels pol x n).card : ℝ≥0∞)

/-- Expected cost when every observation costs one and every new coin costs a further `c`
(for `c ≥ 0`; a negative `c` is read as `0` through `ENNReal.ofReal`). -/
def chargedExpectedWork {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    (c : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, (totalProcessWork z.2 + ENNReal.ofReal c * totalCreated (A.policy z.1.1) z.2)
    ∂experimentLaw μ A q

/-- Uniform budget `B` for the charged cost with fee `c` per created coin (a negative `c`
is read as `0`). -/
def ChargedUniformBudget {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (c B : ℝ) : Prop :=
  ∀ q : SignLaw, chargedExpectedWork μ A q c ≤ ENNReal.ofReal B

/-- Minimax RMS risk over all adaptive estimators with charged uniform budget `B`. -/
def chargedMinimaxRisk (μ : Measure Gap) [IsProbabilityMeasure μ] (c B : ℝ) : ℝ≥0∞ :=
  sInf {r | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    ChargedUniformBudget μ A c B ∧ r = maximalRMSRisk μ A}

/-- Every created coin receives an observation (a.s.): each created label was selected
at an earlier observed step, and created coins are at most observations. -/
def CreatedObservedStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw),
    ∀ᵐ z ∂experimentLaw μ A q,
      (∀ n : ℕ, ∀ i ∈ createdLabels (A.policy z.1.1) z.2 n,
        ∃ k < n, A.policy z.1.1 (processHistory z.2 k) = some i ∧ (z.2 k).isSome) ∧
      totalCreated (A.policy z.1.1) z.2 ≤ totalProcessWork z.2

/-- A fee `c ≥ 0` per new coin changes the expected cost by at most the factor `1 + c`. -/
def ChargedWorkStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (c : ℝ), 0 ≤ c →
    expectedWork μ A q ≤ chargedExpectedWork μ A q c ∧
    chargedExpectedWork μ A q c ≤ ENNReal.ofReal (1 + c) * expectedWork μ A q

/-- One budget-indexed family, chosen before the gap law, keeps the uniform budget `B`, the
charged budget `(1+c)B` for every fee `c ≥ 0`, and RMS risk at most `12 ω(B^{-1/2})`. -/
def ChargedBlindUpperStatement : Prop :=
  ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → AdaptiveEstimator R),
    ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      UniformBudget μ (rule B) B ∧
      (∀ c : ℝ, 0 ≤ c → ChargedUniformBudget μ (rule B) c ((1 + c) * B)) ∧
      maximalRMSRisk μ (rule B) ≤ ENNReal.ofReal (12 * modulus μ (1 / Real.sqrt B))

/-- Minimax sandwich (beyond the source). -/
def ChargedMinimaxStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (c B : ℝ), 0 ≤ c →
    minimaxRisk μ B ≤ chargedMinimaxRisk μ c B ∧
    chargedMinimaxRisk μ c B ≤ minimaxRisk μ (B / (1 + c))

/-- The rate survives the fee with explicit constants (beyond the source). -/
def ChargedRateStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (c B : ℝ), 0 ≤ c → 1 + c ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) ≤ chargedMinimaxRisk μ c B ∧
    chargedMinimaxRisk μ c B ≤
      ENNReal.ofReal (12 * Real.sqrt (1 + c) * modulus μ (1 / Real.sqrt B))

end ThresholdHC.CreationCharge
