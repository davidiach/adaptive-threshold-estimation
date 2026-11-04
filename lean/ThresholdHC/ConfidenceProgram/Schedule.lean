import ThresholdHC.Confidence.BudgetScale
import ThresholdHC.HardBudget.BudgetScale

noncomputable section
open scoped ENNReal
namespace ThresholdHC.ConfidenceProgram

def groups (δ : ℝ) : ℕ := ⌈4*Real.log (1/δ)⌉₊
def copyCount (δ : ℝ) : ℝ := 2*(groups δ:ℝ)+1
def baseBudget (B δ : ℝ) : ℝ := B/(8*copyCount δ)

theorem schedule_failure {δ : ℝ} (hd : 0 < δ) :
    (3/4:ℝ)^(groups δ)/2 ≤ δ := by
  let ℓ := Real.log (1/δ)
  have hm : 4*ℓ ≤ (groups δ:ℝ) := Nat.le_ceil _
  have hl : Real.log (3/4:ℝ) ≤ -(1/4) := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3/4)]
  have he := Real.exp_le_exp.mpr (show (groups δ:ℝ)*Real.log (3/4:ℝ) ≤ -ℓ by
    nlinarith only [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (groups δ)),hm])
  dsimp only [ℓ] at he
  rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<3/4),Real.exp_neg,Real.exp_log (one_div_pos.mpr hd)] at he
  have hs : (3/4:ℝ)^(groups δ) ≤ δ := by simpa [ℓ] using he
  linarith [pow_nonneg (by norm_num : (0:ℝ)≤3/4) (groups δ)]

theorem baseBudget_scale {B δ : ℝ} (hb : 0 < B) (hd : 0 < δ) (hu : δ ≤ 1/4) :
    0 < baseBudget B δ ∧ baseBudget B δ ≤ B/Real.log (1/δ) ∧
    Real.sqrt ((B/Real.log (1/δ))/baseBudget B δ) ≤ Real.sqrt 88 := by
  let ℓ := Real.log (1/δ)
  have h1 : 1 ≤ ℓ := ThresholdHC.Confidence.confidence_log_ge_one hd hu
  have hl : 0 < ℓ := by linarith
  have hm : 4*ℓ ≤ (groups δ:ℝ) := Nat.le_ceil _
  have hm' : (groups δ:ℝ) < 4*ℓ+1 := Nat.ceil_lt_add_one (by positivity : 0 ≤ 4*ℓ)
  have hc : 0 < copyCount δ := by unfold copyCount; positivity
  have hlo : ℓ ≤ 8*copyCount δ := by dsimp [copyCount]; linarith
  have hhi : 8*copyCount δ ≤ 88*ℓ := by dsimp [copyCount]; linarith
  refine ⟨div_pos hb (by positivity),div_le_div_of_nonneg_left hb.le hl hlo,?_⟩
  apply Real.sqrt_le_sqrt
  change (B/ℓ)/(B/(8*copyCount δ)) ≤ 88
  rw [show (B/ℓ)/(B/(8*copyCount δ)) = (8*copyCount δ)/ℓ by field_simp]
  exact (div_le_iff₀ hl).2 hhi

end ThresholdHC.ConfidenceProgram
