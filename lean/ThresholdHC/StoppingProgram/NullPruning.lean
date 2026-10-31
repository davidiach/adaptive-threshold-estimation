import ThresholdHC.StoppingProgram.PositiveValue
import ThresholdHC.StoppingProgram.OutputChoices

/-! Removing output coordinates at states null under an interior reference
preserves every actual prior mean and all feasible certificate guarantees. -/

noncomputable section
open MeasureTheory

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw)

def pruneArray {N : ℕ} (μ : Measure Gap) (q : SignLaw) (u : CountState N → ℝ) : CountState N → ℝ :=
  fun s => if countCoefficient μ q s = 0 then 0 else u s

def pruneFlow {N : ℕ} (μ : Measure Gap) (q : SignLaw) (f : Flow N) : Flow N :=
  withOutputs f (pruneArray μ q f.outputWeight) (pruneArray μ q f.momentWeight)

theorem pruneFlow_cone {N : ℕ} (μ : Measure Gap) (q : SignLaw) (f : Flow N)
    (hf : FlowCone f) : FlowCone (pruneFlow μ q f) := by
  apply hf.withOutputs
  · intro s
    unfold pruneArray
    split_ifs <;> first | exact le_rfl | exact hf.moment_nonneg s
  · simp [pruneArray,hf.root_output]
  · simp [pruneArray,hf.root_moment]
  · intro s
    unfold pruneArray
    split_ifs <;> first | simp | exact hf.perspective s

theorem countMean_pruneArray {N : ℕ} (μ : Measure Gap) (q qref : SignLaw)
    (hnull : ∀ s : CountState N, countCoefficient μ qref s = 0 → countCoefficient μ q s = 0)
    (u : CountState N → ℝ) : countMean μ q (pruneArray μ qref u) = countMean μ q u := by
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : countCoefficient μ qref s = 0
  · simp [pruneArray,hs,hnull s hs]
  · simp [pruneArray,hs]

def pruneCertificate {N : ℕ} (μ : Measure Gap) (q : SignLaw) (C : Certificate N) : Certificate N :=
  ⟨pruneFlow μ q C.flow,C.offset,C.bias,C.variance⟩

theorem pruneCertificate_feasible {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B r : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1/2) (C : Certificate N) (hC : Feasible μ ρ B C) :
    Feasible μ ρ B (pruneCertificate μ (constantPrior r ⟨hr.le,by linarith⟩) C) := by
  refine ⟨pruneFlow_cone μ _ C.flow hC.cone,hC.bias_nonneg,hC.variance_nonneg,?_,?_,hC.work_bound⟩
  · intro q hq
    change |C.offset+countMean μ q (pruneArray μ _ C.flow.outputWeight)-ThresholdHC.Tier6.signMean μ q.val| ≤ C.bias
    rw [countMean_pruneArray μ q _ (fun s => constantPrior_null_state μ q s hr hrhalf)]
    exact hC.bias_bound q hq
  · intro q hq
    change countMean μ q (pruneArray μ _ C.flow.momentWeight) ≤ C.variance
    rw [countMean_pruneArray μ q _ (fun s => constantPrior_null_state μ q s hr hrhalf)]
    exact hC.variance_bound q hq

def NullPruned {N : ℕ} (μ : Measure Gap) (q : SignLaw) (C : Certificate N) : Prop :=
  ∀ s : CountState N, countCoefficient μ q s = 0 → C.flow.outputWeight s = 0 ∧ C.flow.momentWeight s = 0

theorem pruneCertificate_pruned {N : ℕ} (μ : Measure Gap) (q : SignLaw) (C : Certificate N) :
    NullPruned μ q (pruneCertificate μ q C) := by
  intro s hs
  simp [pruneCertificate,pruneFlow,withOutputs,pruneArray,hs]

end ThresholdHC.StoppingProgram
