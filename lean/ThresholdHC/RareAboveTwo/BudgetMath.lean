import ThresholdHC.RareAboveTwo.Model
import ThresholdHC.Tier6.RiskReduction
import Mathlib.Algebra.Order.Floor.Ring

/-! Budget allocation and the exact saturation crossover. -/
noncomputable section
namespace ThresholdHC.RareAboveTwo

def batchIndex (T B : ℝ) : ℕ := ⌊B/(2*T)⌋₊

theorem batchIndex_bounds (T B : ℝ) (hT : 0 < T) (hB : 2*T ≤ B) :
    ((batchIndex T B : ℝ)+1)*T ≤ B ∧ B/(2*T) ≤ (batchIndex T B : ℝ)+1 := by
  have hB0 : 0 ≤ B := by linarith
  have hf := Nat.floor_le (by positivity : 0 ≤ B/(2*T))
  have hf' := Nat.lt_floor_add_one (B/(2*T))
  change (batchIndex T B : ℝ) ≤ B/(2*T) at hf
  change B/(2*T) < (batchIndex T B : ℝ)+1 at hf'
  refine ⟨?_,hf'.le⟩
  have h := mul_le_mul_of_nonneg_right hf hT.le
  have he : B/(2*T)*T = B/2 := by field_simp
  rw [he] at h
  nlinarith

def rateCoefficient (W : ℝ) : ℝ := Real.sqrt (56*W)
def upperRate (W a ρ B : ℝ) : ℝ := rateCoefficient W*Real.sqrt ρ/(a*Real.sqrt B)

theorem upperRate_pos (W a ρ B : ℝ) (hW : 0 < W) (ha : 0 < a) (hρ : 0 < ρ) (hB : 0 < B) :
    0 < upperRate W a ρ B := by unfold upperRate rateCoefficient; positivity

theorem upperRate_square (W a ρ B : ℝ) (hW : 0 ≤ W) (hρ : 0 ≤ ρ) (hB : 0 ≤ B) :
    (upperRate W a ρ B)^2 = 56*ρ*(W/a^2)/B := by
  unfold upperRate rateCoefficient
  rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 56*W),Real.sq_sqrt hρ,Real.sq_sqrt hB]
  ring

theorem large_budget_bounds (W a ρ B : ℝ) (hW : 0 < W) (ha : 0 < a)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hlarge : 224*(W/a^2)/ρ ≤ B) :
    ((batchIndex (W/a^2) B : ℝ)+1)*(W/a^2) ≤ B ∧
    28*ρ/((batchIndex (W/a^2) B : ℝ)+1) ≤ (upperRate W a ρ B)^2 ∧
    upperRate W a ρ B ≤ ρ/2 := by
  have hT : 0 < W/a^2 := by positivity
  have hB : 0 < B := (div_pos (by positivity : 0 < 224*(W/a^2)) hρ).trans_le hlarge
  have hb := (div_le_iff₀ hρ).mp hlarge
  have hb' := mul_le_mul_of_nonneg_left hρ1 hB.le
  have hBT : 2*(W/a^2) ≤ B := by linarith
  obtain ⟨hn,hn'⟩ := batchIndex_bounds (W/a^2) B hT hBT
  refine ⟨hn,?_,?_⟩
  · rw [upperRate_square W a ρ B hW.le hρ.le hB.le]
    calc
      _ ≤ 28*ρ/(B/(2*(W/a^2))) := div_le_div_of_nonneg_left (by positivity) (by positivity) hn'
      _ = _ := by field_simp; ring
  · have hs : (upperRate W a ρ B)^2 ≤ (ρ/2)^2 := by
      rw [upperRate_square W a ρ B hW.le hρ.le hB.le]
      apply (div_le_iff₀ hB).2
      have h := mul_le_mul_of_nonneg_left hb hρ.le
      nlinarith only [h]
    nlinarith [upperRate_pos W a ρ B hW ha hρ hB]

theorem small_budget_bound (W a ρ B : ℝ) (hW : 0 < W) (ha : 0 < a)
    (hρ : 0 < ρ) (hB : 0 < B) (hsmall : B < 224*(W/a^2)/ρ) :
    ρ/2 ≤ upperRate W a ρ B := by
  have hb := (lt_div_iff₀ hρ).mp hsmall
  have hs : (ρ/2)^2 ≤ (upperRate W a ρ B)^2 := by
    rw [upperRate_square W a ρ B hW.le hρ.le hB.le]
    apply (le_div_iff₀ hB).2
    have h := mul_le_mul_of_nonneg_left hb.le hρ.le
    nlinarith only [h]
  nlinarith [upperRate_pos W a ρ B hW ha hρ hB]

end ThresholdHC.RareAboveTwo
