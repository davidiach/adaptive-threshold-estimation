import ThresholdHC.FiniteSelectionApproximation.Objective
import ThresholdHC.FiniteSelectionApproximation.Frontier
import ThresholdHC.FiniteSelectionApproximation.Endpoints

noncomputable section
open MeasureTheory
open scoped Classical ENNReal
namespace ThresholdHC.FiniteSelectionApproximation
open ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.BandwiseSuffix
open ThresholdHC.BandCostSelection ThresholdHC.GapLawMenus ThresholdHC.SelectionApproximation

def lawFrontier (μ : Measure Gap) (hF : μ.support.Finite) (B ε : ℝ) : Finset (List (Finset Gap)) :=
  frontier (cost μ) (saving μ (1/Real.sqrt B)) (lawMenus μ hF) ε

/-- A finite-law approximation theorem for every finite probability law on the
gap space, and therefore in particular every rational finite law. This specifies
the mathematical finite scheme and certified rational endpoints. It does not
assert bit complexity or refinement to a Python/PRNG implementation. -/
def FiniteLawApproximationStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (hF : μ.support.Finite)
    (ρ B ε : ℝ), 0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < ε → ε ≤ 1 →
    let ms := lawMenus μ hF
    let r := minCost (cost μ) ms
    let R := maxCost (cost μ) ms/r
    let L := logScale R
    let M := cellCount ms.length R ε
    let S := stateCount R L M
    let Q := hF.toFinset.card+(occupiedBands hF.toFinset).length
    let J := menuObjective μ ρ B
    let K := (selection μ ρ B).toReal
    ∃ N ≤ sufficientPrecision (positiveFloor ρ B r) (beta ε),
      ∃ xs ∈ lawFrontier μ hF B ε, ∃ l u : ℚ,
        traceSet xs ∈ suffixChoices hF.toFinset ∧
        ENNReal.ofReal (J xs) = min (ENNReal.ofReal ρ)
          (selectionObjective μ ρ B (μ.restrict (traceSet xs))) ∧
        u = upperEndpoint N (J xs) ∧
        (∀ ys ∈ lawFrontier μ hF B ε, u ≤ upperEndpoint N (J ys)) ∧
        (∀ ys ∈ lawFrontier μ hF B ε, (l:ℝ) ≤ J ys) ∧
        0 < (l:ℝ) ∧ (l:ℝ)/beta ε ≤ K ∧ K ≤ J xs ∧ J xs ≤ (u:ℝ) ∧
        (u:ℝ) ≤ (1+ε)*((l:ℝ)/beta ε) ∧
        (∀ rest, rest.IsSuffix ms →
          (trimSolve (binKey r M) (cost μ) (summary (cost μ) r ε)
            (saving μ (1/Real.sqrt B)) rest).card ≤ S) ∧
        extensionCount (binKey r M) (cost μ) (summary (cost μ) r ε)
          (saving μ (1/Real.sqrt B)) ms ≤ Q*S

end ThresholdHC.FiniteSelectionApproximation
