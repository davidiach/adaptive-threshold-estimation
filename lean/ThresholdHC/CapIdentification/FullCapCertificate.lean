import ThresholdHC.CapIdentification.CountBounds
import ThresholdHC.StoppingProgram.FullCapFlow

/-! A prescribed full-depth output array produces finite-cap certificates
with its uniform bias and a variance term C/B. The constant may depend on
the fixed cap and output array, which is sufficient for the budget limit. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.StoppingProgram ThresholdHC.RareAboveTwo

def terminalArray {N : ℕ} (y : CountState N → ℝ) (s : CountState N) : ℝ :=
  if s.1.val = N then y s else 0

def outputSquareSum {N : ℕ} (y : CountState N → ℝ) : ℝ := ∑ s, (y s)^2

def fullOutputFlow (N : ℕ) (r : ℝ) (y : CountState N → ℝ) : Flow N where
  stopWeight s := r*(fullCapFlow N).stopWeight s
  continueWeight s := r*(fullCapFlow N).continueWeight s
  outputWeight := terminalArray y
  momentWeight := terminalArray (fun s => (y s)^2/r)

theorem arrayAt_const_mul {N : ℕ} (u : CountState N → ℝ) (r : ℝ) (n k : ℕ) :
    arrayAt (fun s => r*u s) n k = r*arrayAt u n k := by
  unfold arrayAt
  split_ifs <;> simp

theorem outputSquareSum_nonneg {N : ℕ} (y : CountState N → ℝ) : 0 ≤ outputSquareSum y :=
  Finset.sum_nonneg (fun s _ => sq_nonneg (y s))

theorem outputSquareSum_ge {N : ℕ} (y : CountState N → ℝ) (s : CountState N) : (y s)^2 ≤ outputSquareSum y :=
  Finset.single_le_sum (fun t _ => sq_nonneg (y t)) (Finset.mem_univ s)

theorem fullOutputFlow_cone {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 < r) (y : CountState N → ℝ) :
    FlowCone (fullOutputFlow N r y) := by
  have hf := fullCapFlow_cone hN
  constructor
  · intro s
    exact mul_nonneg hr.le (hf.stop_nonneg s)
  · intro s
    exact mul_nonneg hr.le (hf.continue_nonneg s)
  · intro s
    dsimp only [fullOutputFlow,terminalArray]
    split_ifs <;> positivity
  · change r*(fullCapFlow N).stopWeight (rootState N) = 0
    rw [hf.root_stop,mul_zero]
  · simp only [fullOutputFlow,terminalArray,rootState,show ¬0 = N by omega,ite_false]
  · simp only [fullOutputFlow,terminalArray,rootState,show ¬0 = N by omega,ite_false]
  · intro s hs
    change r*(fullCapFlow N).continueWeight s = 0
    rw [hf.terminal s hs,mul_zero]
  · intro s hs
    change r*(fullCapFlow N).stopWeight s+r*(fullCapFlow N).continueWeight s = _
    simp only [fullOutputFlow,arrayAt_const_mul]
    rw [← mul_add,hf.recursion s hs]
    ring
  · intro s
    dsimp only [fullOutputFlow,terminalArray,fullCapFlow]
    by_cases hs : s.1.val = N
    · simp only [hs,ite_true,mul_one]
      rw [mul_div_cancel₀ _ hr.ne']
    · simp only [hs,ite_false,mul_zero,zero_pow (by decide : 2 ≠ 0),le_refl]

theorem fullOutputFlow_work_bound {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) {r : ℝ} (hr : 0 ≤ r) (y : CountState N → ℝ) :
    countMean μ q (fullOutputFlow N r y).continueWeight ≤ r*countEnvelope N := by
  apply countMean_le_envelope μ q _ hr
  · intro s
    dsimp only [fullOutputFlow,fullCapFlow]
    split_ifs <;> positivity
  · intro s
    dsimp only [fullOutputFlow,fullCapFlow]
    split_ifs <;> simp_all

theorem fullOutputFlow_variance_bound {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) {r : ℝ} (hr : 0 < r) (y : CountState N → ℝ) :
    countMean μ q (fullOutputFlow N r y).momentWeight ≤ (outputSquareSum y/r)*countEnvelope N := by
  apply countMean_le_envelope μ q _ (div_nonneg (outputSquareSum_nonneg y) hr.le)
  · intro s
    dsimp only [fullOutputFlow,terminalArray]
    split_ifs <;> positivity
  · intro s
    dsimp only [fullOutputFlow,terminalArray]
    split_ifs
    · exact div_le_div_of_nonneg_right (outputSquareSum_ge y s) hr.le
    · exact div_nonneg (outputSquareSum_nonneg y) hr.le

theorem full_output_program_upper (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) {N : ℕ} (hN : 0 < N) (y : CountState N → ℝ) (c b : ℝ) (hb : 0 ≤ b)
    (hbias : ∀ q : SignLaw, RarePrior μ ρ q → |c+countMean μ q (terminalArray y)-signMean μ q.val| ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, 0 < B → programSquared μ ρ B N ≤ ENNReal.ofReal (b^2+C/B) := by
  let W := countEnvelope N
  let C := W^2*outputSquareSum y
  have hW : 0 < W := countEnvelope_pos N
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg W) (outputSquareSum_nonneg y)
  refine ⟨C,hC,?_⟩
  intro B hB
  let r := B/W
  have hr : 0 < r := div_pos hB hW
  let cert : Certificate N := ⟨fullOutputFlow N r y,c,b,C/B⟩
  have hcert : Feasible μ ρ B cert := by
    refine ⟨fullOutputFlow_cone hN hr y,hb,div_nonneg hC hB.le,hbias,?_,?_⟩
    · intro q _
      have hh := fullOutputFlow_variance_bound μ q hr y
      have he : (outputSquareSum y/r)*countEnvelope N = C/B := by
        dsimp only [r,C,W]
        field_simp
      exact hh.trans_eq he
    · intro q _
      have hh := fullOutputFlow_work_bound μ q hr.le y
      have he : r*countEnvelope N = B := by
        change (B/W)*W = B
        exact div_mul_cancel₀ _ hW.ne'
      exact hh.trans_eq he
  exact sInf_le ⟨cert,hcert,rfl⟩

end ThresholdHC.CapIdentification
