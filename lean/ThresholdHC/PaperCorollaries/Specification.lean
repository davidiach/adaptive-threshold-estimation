import ThresholdHC.Envelope.Minimax
import ThresholdHC.HardBudget.Ordinary
import ThresholdHC.PowerWindow.Specification

/-! Target statements for corollaries and remarks that the guides state as
paper arguments on top of Lean-checked theorems.

* The sharp lower coefficient `1/6` and the upper constant `12` of the RMS law
  carried to an unknown gap law below a stochastic envelope, and the
  coefficient `1/6` carried to a pathwise observation cap.
* The paper's divergence sequence `ρ_n = exp(-exp n)`, `B_n = ρ_n^{-2}` at the
  quadratic law, along which the ratio of the minimax risk to `Ψ` diverges.

They use only the envelope minimax risk of `Envelope`, the hard-cap minimax risk
of `HardBudget`, the rare-event minimax risk and `Ψ` of `RareAboveTwo`, and the
original modulus. The proofs are in the other modules of this directory. -/
noncomputable section
namespace ThresholdHC.PaperCorollaries
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
open scoped ENNReal

/-- Under a stochastic envelope `μ`, the minimax RMS risk over every gap law
below `μ` is between one sixth and twelve times `ω_μ(B^{-1/2})`. -/
def EnvelopeRMSStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) ≤ ThresholdHC.Envelope.minimaxRMS μ B ∧
    ThresholdHC.Envelope.minimaxRMS μ B ≤ ENNReal.ofReal (12 * modulus μ (1 / Real.sqrt B))

/-- Under a pathwise cap of `⌊B⌋` observations, the minimax RMS risk is at least
one sixth of the modulus. -/
def HardSharpLowerStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) ≤ ThresholdHC.HardBudget.hardMinimaxRisk μ B

/-- At the quadratic law `F(d) = (4d)^2`, along `ρ_n = exp(-exp n)` and
`B_n = ρ_n^{-2}` the minimax risk is at least `7·10^{-20} √(1 + log(1 + log(1/ρ_n)))`
times `Ψ_{μ,ρ_n}(B_n^{-1/2})` for every `n ≥ 3`, and that factor is at least
`√(1 + n)`, so the ratio diverges (v6 §14.4 and Appendix F). -/
def PsiSequenceStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], ExactPowerLaw μ 2 (1/4) → ∀ n : ℕ, 3 ≤ n →
    let ρ := Real.exp (-Real.exp n)
    let B := 1 / ρ ^ 2
    ENNReal.ofReal (7 * (10 : ℝ)⁻¹ ^ 20 * Real.sqrt (1 + Real.log (1 + Real.log (1/ρ)))) *
        rarePsi μ ρ (1 / Real.sqrt B) ≤ rareMinimaxRisk μ ρ B ∧
    Real.sqrt (1 + n) ≤ Real.sqrt (1 + Real.log (1 + Real.log (1/ρ)))

end ThresholdHC.PaperCorollaries
