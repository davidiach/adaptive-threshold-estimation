import ThresholdHC.Tier6.AlgorithmModel
import ThresholdHC.Tier3.OptimizerModel

/-! Rare priors in the unchanged observable experiment. Magnitudes and signs
remain hidden. Rarity is a bound on the integral of the sign law, not a
pointwise bound. The power class is defined by its actual distribution function. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Tier6

def PowerMargin (μ : Measure Gap) (α a : ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → x < a → μ.real {d | (d : ℝ) ≤ x} ≤ (x/a)^α

def ExactPowerLaw (μ : Measure Gap) (α a : ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → μ.real {d | (d : ℝ) ≤ x} = min 1 ((x/a)^α)

def RarePrior (μ : Measure Gap) (ρ : ℝ) (q : SignLaw) : Prop := signMean μ q.val ≤ ρ

def RareBudget {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (ρ B : ℝ) : Prop :=
  ∀ q : SignLaw, RarePrior μ ρ q → expectedWork μ A q ≤ ENNReal.ofReal B

def rareRisk {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (ρ : ℝ) : ℝ≥0∞ :=
  ⨆ (q : SignLaw) (_ : RarePrior μ ρ q),
    rootMeanRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val)

def rareMinimaxRisk (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    RareBudget μ A ρ B ∧ t = rareRisk μ A ρ}

def aboveTwoRate (a ρ B : ℝ) : ℝ := min ρ (Real.sqrt ρ/(a*Real.sqrt B))

def rarePsi (μ : Measure Gap) (ρ h : ℝ) : ℝ≥0∞ :=
  ⨆ (v : Gap → ℝ) (_ : Tier3.FeasibleAllocation μ ρ v),
    ENNReal.ofReal (Tier3.rareObjective μ (fun d => (d : ℝ)) h v)

end ThresholdHC.RareAboveTwo
