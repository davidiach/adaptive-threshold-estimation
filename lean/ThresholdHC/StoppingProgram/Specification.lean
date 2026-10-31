import ThresholdHC.StoppingProgram.Model

/-! Full stopping-program targets. Defining these propositions does not prove
them. No strong-duality, compactness, realization, or testing premise occurs
in the final statements. The entropy-tail statistical lower target is separate. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

def ProgramUpperStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (N : ℕ),
    0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < N → rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N

def AttainedDualStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (N : ℕ),
    0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < N →
    programSquared μ ρ B N = dualValue μ ρ B N ∧
    ∃ (C : Certificate N) (Q : FourPriors),
      Feasible μ ρ B C ∧ Admissible μ ρ Q ∧
      certificateSquared C = programSquared μ ρ B N ∧
      dualRatio μ B N Q = programSquared μ ρ B N ∧
      0 < programSquared μ ρ B N ∧ informationRatio μ N Q < ⊤

def certificateCap (ρ B : ℝ) : ℕ := ⌈64*max B (ρ*B^2)⌉₊

def FiniteCertificateStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
    rareMinimaxRisk μ ρ B ≤ programValue μ ρ B (certificateCap ρ B) ∧
    programValue μ ρ B (certificateCap ρ B) ≤ 16*rareMinimaxRisk μ ρ B

end ThresholdHC.StoppingProgram
