import ThresholdHC.RareAboveTwo.Model

/-! Full observable targets, fixed before supporting proofs. Constants may
be conservative: the rate, all parameter regimes, global rarity class and
law-independent upper family are the targets, not the paper's numeric constants.
No statistical bound, realization, integrability or external theorem is assumed. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Tier6

def PowerLawExistenceStatement : Prop :=
  ∀ α a : ℝ, 0 < α → 0 < a → a ≤ 1/2 →
    ∃ μ : Measure Gap, IsProbabilityMeasure μ ∧ ExactPowerLaw μ α a

def RareSingleCoinStatement : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ single : ℝ → ℝ → AdaptiveEstimator ℕ,
    (∀ a ρ j xs, (single a ρ).policy j xs = none ∨ (single a ρ).policy j xs = some 0) ∧
    ∀ α : ℝ, 2 < α → ∃ W : ℝ, 0 < W ∧
    ∀ a ρ : ℝ, 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], PowerMargin μ α a →
    ∀ q : SignLaw, RarePrior μ ρ q →
      Integrable (populationOutput (single a ρ)) (experimentLaw μ (single a ρ) q) ∧
      (∫ z, populationOutput (single a ρ) z ∂experimentLaw μ (single a ρ) q) = signMean μ q.val ∧
      (∫⁻ z, ENNReal.ofReal ((populationOutput (single a ρ) z)^2)
        ∂experimentLaw μ (single a ρ) q) ≤ ENNReal.ofReal (K*ρ) ∧
      expectedWork μ (single a ρ) q ≤ ENNReal.ofReal (W/a^2)

def RareSupportedLowerStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ a ρ B : ℝ,
    0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 1 ≤ B →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], (∀ᵐ d : Gap ∂μ, (d : ℝ) ≤ a) →
    ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R), RareBudget μ A ρ B →
      ENNReal.ofReal (c*aboveTwoRate a ρ B) ≤ rareRisk μ A ρ

def AboveTwoUpperStatement : Prop :=
  ∀ α : ℝ, 2 < α → ∃ C : ℝ, 0 < C ∧
    ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → ℝ → ℝ → AdaptiveEstimator R),
    ∀ a ρ B : ℝ, 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 1 ≤ B →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], PowerMargin μ α a →
      RareBudget μ (rule a ρ B) ρ B ∧
      rareRisk μ (rule a ρ B) ρ ≤ ENNReal.ofReal (min (ρ/2) (C*Real.sqrt ρ/(a*Real.sqrt B)))

def AboveTwoMinimaxStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ α : ℝ, 2 < α → ∃ C : ℝ, 0 < C ∧
    ∀ a ρ B : ℝ, 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 1 ≤ B →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], ExactPowerLaw μ α a →
      ENNReal.ofReal (c*aboveTwoRate a ρ B) ≤ rareMinimaxRisk μ ρ B ∧
      rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (C*aboveTwoRate a ρ B)

def AboveTwoPsiStatement : Prop :=
  ∀ α : ℝ, 2 < α → ∃ C : ℝ, 0 < C ∧ ∀ a ρ h : ℝ,
    0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < h →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], ExactPowerLaw μ α a →
      ENNReal.ofReal (min ρ (h*Real.sqrt ρ/a)) ≤ rarePsi μ ρ h ∧
      rarePsi μ ρ h ≤ ENNReal.ofReal (C*min ρ (h*Real.sqrt ρ/a))

def RareNonvacuityStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ), 0 ≤ ρ → 0 ≤ B →
    (∃ A : AdaptiveEstimator Unit, RareBudget μ A ρ B ∧ rareRisk μ A ρ ≤ ENNReal.ofReal (ρ/2)) ∧
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (ρ/2)

end ThresholdHC.RareAboveTwo

