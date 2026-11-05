import ThresholdHC.QuantileSharpLaw.Interaction

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.EntropyTailQuantile

def boundaryUnit {ι : Type*} : Option ι → ℝ
  | none => 1
  | some _ => 0

theorem boundaryUnit_nonneg {ι : Type*} (i : Option ι) : 0 ≤ boundaryUnit i := by
  cases i <;> norm_num [boundaryUnit]

theorem boundaryUnit_entropy {ι : Type*} [Fintype ι] :
    costEntropy (boundaryUnit : Option ι → ℝ) = 1 := by
  simp [costEntropy,costTotal,Fintype.sum_option,boundaryUnit]

theorem augmented_entropy_lower {ι : Type*} [Fintype ι] {v : Option ι → ℝ}
    (hv : ∀ i, 0 ≤ v i) :
    1+costEntropy v ≤ costEntropy (fun i => v i+boundaryUnit i) := by
  have h := costEntropy_superadditive hv boundaryUnit_nonneg
  rw [boundaryUnit_entropy] at h
  linarith only [h]

theorem costEntropy_option_identity {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ) :
    costEntropy (bumpedCost a v 0) = a+costEntropy v+costInteraction a (costTotal v) := by
  rw [bumpedCost_entropy]
  norm_num only [zero_pow,add_zero]
  unfold costEntropy costInteraction
  ring

theorem zero_boundary_entropy {ι : Type*} [Fintype ι] {v : Option ι → ℝ} (hv : v none=0) :
    costEntropy v = costEntropy (fun i => v (some i)) ∧ costTotal v = costTotal (fun i => v (some i)) := by
  have ht : costTotal v = costTotal (fun i => v (some i)) := by
    simp only [costTotal,Fintype.sum_option,hv,zero_add]
  refine ⟨?_,ht⟩
  simp only [costEntropy,ht,Fintype.sum_option,hv,negMulLog_zero,zero_add]

theorem augmented_entropy_zero_boundary {ι : Type*} [Fintype ι] {v : Option ι → ℝ}
    (hv : v none=0) :
    costEntropy (fun i => v i+boundaryUnit i) =
      1+costEntropy v+costInteraction (costTotal v) 1 := by
  have he : (fun i => v i+boundaryUnit i) = bumpedCost 1 (fun i => v (some i)) 0 := by
    funext i
    cases i <;> simp [bumpedCost,boundaryUnit,hv]
  rw [he,costEntropy_option_identity,← (zero_boundary_entropy hv).1,
    ← (zero_boundary_entropy hv).2,costInteraction_symm]

theorem compressed_entropy_identity {ι : Type*} [Fintype ι] (E : ℝ) {b : Option ι → ℝ}
    (hb : b none=0) :
    costEntropy (bumpedCost E (fun i => b (some i)) 0) =
      E+costEntropy b+costInteraction E (costTotal b) := by
  rw [costEntropy_option_identity,← (zero_boundary_entropy hb).1,← (zero_boundary_entropy hb).2]

end ThresholdHC.QuantileSharpLaw
