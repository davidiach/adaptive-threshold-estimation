import ThresholdHC.BandwiseSuffix.Specification
import ThresholdHC.EntropyTail.HardSelection

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.BandwiseSuffix
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

/-- On finite support, only finitely many hard restrictions occur. Thus the hard-selection
infimum is attained, even when we compare it with all fractional submeasures. -/
theorem exists_optimal_hard (μ : Measure Gap) [IsProbabilityMeasure μ] (hF : μ.support.Finite)
    {ρ B : ℝ} (hρ : 0 < ρ) (hr : ρ ≤ 1/4) (hB : 0 < B) :
    ∃ S : Finset Gap, (S : Set Gap) ⊆ μ.support ∧
      ∀ σ : Measure Gap, σ ≤ μ → selectionObjective μ ρ B (μ.restrict S) ≤ selectionObjective μ ρ B σ := by
  classical
  let F := hF.toFinset
  let obj := fun S : Finset Gap => selectionObjective μ ρ B (μ.restrict S)
  obtain ⟨S,hS,hmin⟩ := F.powerset.exists_min_image obj ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
  refine ⟨S, fun x hx => hF.mem_toFinset.mp (Finset.mem_powerset.mp hS hx), ?_⟩
  have hl : obj S ≤ ⨅ (s : Set Gap) (_ : MeasurableSet s), selectionObjective μ ρ B (μ.restrict s) := by
    refine le_iInf₂ fun s _ => ?_
    let A := F.filter (· ∈ s)
    have he : μ.restrict (A : Set Gap) = μ.restrict s := by
      apply Measure.restrict_congr_set
      filter_upwards [μ.support_mem_ae] with x hx
      simp [A, F, hx]
    rw [← he]
    exact hmin A (Finset.mem_powerset.mpr (Finset.filter_subset ..))
  rw [← hard_selection ρ B hρ hr hB μ] at hl
  exact fun σ hσ => hl.trans (iInf₂_le σ hσ)

/-- A point in the finite topological support has strictly positive atomic mass. -/
theorem support_atom_pos {μ : Measure Gap} (hF : μ.support.Finite) {x : Gap} (hx : x ∈ μ.support) :
    0 < μ {x} := by
  let U := (μ.support \ {x})ᶜ
  have hopen : IsOpen U := (hF.sdiff (t := {x})).isClosed.isOpen_compl
  have hmem : x ∈ U := by simp [U]
  have hpos := (Measure.mem_support_iff_forall x).mp hx U (hopen.mem_nhds hmem)
  have he : U =ᵐ[μ] ({x} : Set Gap) := by
    filter_upwards [μ.support_mem_ae] with y hy
    simp [U, hy]
  rwa [measure_congr he] at hpos

end ThresholdHC.BandwiseSuffix
