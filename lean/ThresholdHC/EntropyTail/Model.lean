import ThresholdHC.EntropyTail.CostEntropy
import ThresholdHC.RareAboveTwo.Model

/-!
# The arbitrary-law entropy--tail and closed quantile functionals

The risk and experiment are those already defined in `RareAboveTwo.Model`;
despite that module's name, its rare priors, budget and risk have no power-law
assumption. All cost entropies and risks here retain extended values.

This file defines mathematical objects, not proofs of their characterization.
-/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal BigOperators

namespace ThresholdHC.EntropyTail
open ThresholdHC.Tier6

def bandEdge (j : ℕ) : ℝ := (2:ℝ)⁻¹ ^ (j+1)

def band (j : ℕ) : Set Gap :=
  {d | bandEdge j / 2 < (d:ℝ) ∧ (d:ℝ) ≤ bandEdge j}

def bandCost (σ : Measure Gap) (j : ℕ) : ℝ :=
  ∫ d : Gap in band j, (d:ℝ)⁻¹ ^ 2 ∂σ

/-- Increasing finite-fragment definition; infinite full-law entropy is allowed. -/
def measureCostEntropy (σ : Measure Gap) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (costEntropy (fun j : Fin n => bandCost σ j.val))

def budgetScale (B : ℝ) : ℝ := (sqrt B)⁻¹

def tailModulus (ν : Measure Gap) (h : ℝ) : ℝ :=
  ∫ d : Gap, min 1 (h/(d:ℝ)) ∂ν

def selectionCost (μ σ : Measure Gap) (ρ h : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal h * (ENNReal.ofReal ρ * measureCostEntropy σ) ^ (1/(2:ℝ)) +
    ENNReal.ofReal (tailModulus (μ-σ) h)

def selectionValue (μ : Measure Gap) (ρ B : ℝ) : ℝ≥0∞ :=
  min (ENNReal.ofReal ρ)
    (⨅ (σ : Measure Gap) (_ : σ ≤ μ), selectionCost μ σ ρ (budgetScale B))

/-- Leftmost threshold whose cumulative mass reaches rho. -/
def quantileThreshold (μ : Measure Gap) (ρ : ℝ) : ℝ :=
  sInf {t : ℝ | ρ ≤ μ.real {d : Gap | (d:ℝ) ≤ t}}

def quantileBoundaryFraction (μ : Measure Gap) (ρ : ℝ) : ℝ :=
  (ρ - μ.real {d : Gap | (d:ℝ) < quantileThreshold μ ρ}) /
    μ.real {d : Gap | (d:ℝ) = quantileThreshold μ ρ}

/-- Includes the required fraction of an atom at the quantile threshold. -/
def quantileTail (μ : Measure Gap) (ρ : ℝ) : Measure Gap :=
  μ.restrict {d : Gap | (d:ℝ) < quantileThreshold μ ρ} +
    ENNReal.ofReal (quantileBoundaryFraction μ ρ) •
      μ.restrict {d : Gap | (d:ℝ) = quantileThreshold μ ρ}

def quantileCore (μ : Measure Gap) (ρ : ℝ) : Measure Gap := μ-quantileTail μ ρ

def closedQuantileValue (μ : Measure Gap) (ρ B : ℝ) : ℝ≥0∞ :=
  min (ENNReal.ofReal ρ)
    (ENNReal.ofReal (tailModulus (quantileTail μ ρ) (budgetScale B)) +
      ENNReal.ofReal (budgetScale B) *
        (ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ)) ^ (1/(2:ℝ)))

end ThresholdHC.EntropyTail
