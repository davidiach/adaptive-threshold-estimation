import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped ENNReal Classical
namespace ThresholdHC.LawAdaptation

/-- Coordinatewise agreement with the observed signature. -/
def Compatible {ι κ : Type*} (signature : ι → κ → ℝ)
    (observed : κ → ℝ) (tolerance : ℝ) (i : ι) : Prop :=
  ∀ k, |observed k - signature i k| ≤ tolerance

/-- A separated finite signature identifies the true candidate whenever all
empirical coordinates are accurate. -/
theorem compatible_unique {ι κ : Type*} (signature : ι → κ → ℝ)
    (observed : κ → ℝ) {ε η : ℝ} (hsep : 2*ε < η)
    (hdist : ∀ i j, i ≠ j → ∃ k, η ≤ |signature i k - signature j k|)
    {i j : ι} (hi : Compatible signature observed ε i)
    (hj : Compatible signature observed ε j) : i = j := by
  by_contra hne
  obtain ⟨k, hk⟩ := hdist i j hne
  have ht := abs_sub_le (signature i k) (observed k) (signature j k)
  have hi' : |signature i k - observed k| ≤ ε := by
    simpa only [abs_sub_comm] using hi k
  have hj' := hj k
  linarith

def identify {ι κ : Type*} [Nonempty ι] (signature : ι → κ → ℝ)
    (observed : κ → ℝ) (tolerance : ℝ) : ι :=
  if h : ∃ i, Compatible signature observed tolerance i then Classical.choose h
  else Classical.choice inferInstance

theorem identify_correct {ι κ : Type*} [Nonempty ι] (signature : ι → κ → ℝ)
    (observed : κ → ℝ) {ε η : ℝ} (hsep : 2*ε < η)
    (hdist : ∀ i j, i ≠ j → ∃ k, η ≤ |signature i k - signature j k|)
    (truth : ι) (hgood : Compatible signature observed ε truth) :
    identify signature observed ε = truth := by
  have hex : ∃ i, Compatible signature observed ε i := ⟨truth,hgood⟩
  unfold identify
  rw [dite_eq_left hex]
  exact compatible_unique signature observed hsep hdist (Classical.choose_spec hex) hgood

/-- Selection costs one union bound over tested moments, not over candidates. -/
theorem identify_error_bound {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Nonempty ι] [Fintype κ] (P : Measure Ω) (signature : ι → κ → ℝ)
    (observed : Ω → κ → ℝ) (truth : ι) {ε η : ℝ} (hsep : 2*ε < η)
    (hdist : ∀ i j, i ≠ j → ∃ k, η ≤ |signature i k - signature j k|)
    (failure : κ → ℝ≥0∞)
    (hcoord : ∀ k, P {ω | ε < |observed ω k-signature truth k|} ≤ failure k) :
    P {ω | identify signature (observed ω) ε ≠ truth} ≤ ∑ k, failure k := by
  calc
    _ ≤ P (⋃ k, {ω | ε < |observed ω k-signature truth k|}) := by
      apply measure_mono
      intro ω hω
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      by_contra h
      push Not at h
      exact hω (identify_correct signature (observed ω) hsep hdist truth h)
    _ ≤ ∑ k, P {ω | ε < |observed ω k-signature truth k|} := measure_iUnion_fintype_le P _
    _ ≤ _ := Finset.sum_le_sum (fun k _ => hcoord k)

end ThresholdHC.LawAdaptation

