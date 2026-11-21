import ThresholdHC.Tier6.AlgorithmModel

/-! Target statements for clipping the output of an estimator to `[0,1]`.

Source: `research/2026-11-18-upper-constant/README.md`, section `Results`,
paragraph `Clipping` (with `clipped.py` and `clipped.json`), whose first
sentence begins: Clipping the output to $[0,1]$ can only help. The same file,
section `Where the factor 512 goes`, bullet `Clipping`, adds that clipping
gains a factor of $1.3$ to $1.6$ at the budgets simulated, but little for
large budgets; the summary table of section `Summary` lists the worst
simulated clipped cases.

Of the source's claims, only the qualitative sentence is stated; the two
further statements below are consequences. The simulated factors (a gain of
`1.3` to `1.6`, and worst clipped ratios of about `3.8` at `N = 2^8` and about
`4.9` at `N = 2^10`) are Monte Carlo maxima over a grid of 7 gaps and 3 sign
fractions. They stay simulation evidence and are not stated; nothing here
gives a clipped constant below `12`.

* `UnitClipMonotoneStatement`: the source sentence. The clipped estimator keeps
  the seed law and the policy, hence the experiment and the expected work. It
  does not increase the RMS risk for any sign law, and its maximal RMS risk is
  at most `1`, since outputs and targets both lie in `[0,1]`. The witness `A'`
  is fully determined: its remaining fields `probability`, `policy_measurable`
  and `output_measurable` are propositions.
* `UnitOutputMinimaxStatement` and `ClippedBlindUpper12Statement` are
  consequences that go beyond the source: restricting the minimax class to
  `[0,1]`-valued estimators leaves the minimax RMS risk unchanged, and the
  audited blind family with constant `12` can be taken `[0,1]`-valued, with RMS
  risk at most `min 1 (12*ω(B^{-1/2}))`.

The definitions are those of the original experiment (`Tier6`). -/
noncomputable section
namespace ThresholdHC.ClippedOutput
open MeasureTheory ThresholdHC.Tier6
open scoped ENNReal

/-- Clipping the output to `[0,1]` keeps the seed law and the policy, so it
keeps the expected work and the uniform budget. It does not increase the RMS
risk for any sign law, and it bounds the maximal RMS risk by `1`. -/
def UnitClipMonotoneStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R),
    ∃ A' : AdaptiveEstimator R,
      A'.randomLaw = A.randomLaw ∧ A'.policy = A.policy ∧
      (∀ z, A'.output z = max 0 (min 1 (A.output z))) ∧
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        (∀ q : SignLaw, expectedWork μ A' q = expectedWork μ A q) ∧
        (∀ B : ℝ, UniformBudget μ A' B ↔ UniformBudget μ A B) ∧
        (∀ q : SignLaw,
          rootMeanRisk (experimentLaw μ A' q) (populationOutput A') (signMean μ q.val) ≤
          rootMeanRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val)) ∧
        maximalRMSRisk μ A' ≤ min 1 (maximalRMSRisk μ A)

/-- Restricting the minimax class to estimators with outputs in `[0,1]` does
not change the minimax RMS risk. This goes beyond the source sentence. -/
def UnitOutputMinimaxStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ),
    sInf {r | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      UniformBudget μ A B ∧ (∀ z, 0 ≤ A.output z ∧ A.output z ≤ 1) ∧
      r = maximalRMSRisk μ A} = minimaxRisk μ B

/-- One budget-indexed family with outputs in `[0,1]`, chosen before the gap
law, keeps the uniform budget and has RMS risk at most
`min 1 (12*ω(B^{-1/2}))`. This goes beyond the source sentence. -/
def ClippedBlindUpper12Statement : Prop :=
  ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → AdaptiveEstimator R),
    (∀ B z, 0 ≤ (rule B).output z ∧ (rule B).output z ≤ 1) ∧
    ∀ B : ℝ, 1 ≤ B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      UniformBudget μ (rule B) B ∧
      maximalRMSRisk μ (rule B) ≤ min 1 (ENNReal.ofReal (12 * modulus μ (1 / Real.sqrt B)))

end ThresholdHC.ClippedOutput
