import ThresholdHC.RareAboveTwo.Margin
import ThresholdHC.CriticalUpper.Parameters

/-! Law-independent accuracy calibration. Rarity enters only the positive
boundary and the terminal cap; negative early errors do not pay log(1/rho). -/
noncomputable section
open MeasureTheory Set
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Tier6 ThresholdHC.Uniform713 ThresholdHC.CriticalUpper

def initialLevel (a : ℝ) : ℕ := rarityLevel (a^2)+1

theorem initialLevel_bounds (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1/2) :
    1 ≤ cap (initialLevel a)*a^2 ∧ cap (initialLevel a) ≤ 2/a^2 := by
  have ha2 : a^2 ≤ 1 := by nlinarith
  have hb := rarityLevel_bounds (a^2) (sq_pos_of_pos ha) ha2
  have he : cap (initialLevel a) = 2*(2 : ℝ)^(rarityLevel (a^2)) := by
    simp [initialLevel,cap,pow_succ,mul_comm]
  rw [he]
  constructor
  · have h := (div_lt_iff₀ (sq_pos_of_pos ha)).1 hb.2
    linarith
  · have h := mul_le_mul_of_nonneg_left hb.1 (by norm_num : (0 : ℝ) ≤ 2)
    convert h using 1; ring

def negativeThreshold (j k : ℕ) : ℝ := (4*((j : ℝ)+1)+((k : ℝ)+1))*Real.log 2

def positiveThreshold (ρ : ℝ) (j k : ℕ) : ℝ := negativeThreshold j k+Real.log (1/ρ)

def terminalLevel (ρ : ℝ) (j : ℕ) : ℕ := 2*screenLevel ρ j

theorem negativeThreshold_nonneg (j k : ℕ) : 0 ≤ negativeThreshold j k := by
  unfold negativeThreshold
  positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

theorem positiveThreshold_nonneg (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j k : ℕ) :
    0 ≤ positiveThreshold ρ j k :=
  add_nonneg (negativeThreshold_nonneg j k) (Real.log_nonneg ((one_le_div hρ).2 hρ1))

theorem negativeThreshold_exp (j k : ℕ) :
    Real.exp (-negativeThreshold j k) = screenAccuracy j*(1/2 : ℝ)^(k+1) := by
  have he : negativeThreshold j k = Real.log ((16 : ℝ)^(j+1)*(2 : ℝ)^(k+1)) := by
    unfold negativeThreshold
    rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]
    have hl : Real.log (16 : ℝ) = 4*Real.log 2 := by
      have h := Real.log_pow (2 : ℝ) 4
      norm_num only [show (2 : ℝ)^4 = 16 by norm_num,Nat.cast_ofNat] at h
      exact h
    rw [hl]
    push_cast
    ring
  rw [he,Real.exp_neg,Real.exp_log (by positivity)]
  simp [screenAccuracy,mul_comm]

theorem negativeThreshold_error (j L : ℕ) :
    (∑ k ∈ Finset.range L, Real.exp (-negativeThreshold j k)) ≤ screenAccuracy j := by
  simp_rw [negativeThreshold_exp,← Finset.mul_sum]
  have hsum : (∑ k ∈ Finset.range L, (1/2 : ℝ)^(k+1)) ≤ 1 := by
    have h := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)).mul_left (1/2 : ℝ)
    have hb := h.summable.sum_le_tsum (Finset.range L) (fun _ _ => by positivity)
    rw [h.tsum_eq] at hb
    norm_num only [show (1/2 : ℝ)*(1-1/2)⁻¹ = 1 by norm_num] at hb
    simpa [pow_succ,mul_comm] using hb
  have h := mul_le_mul_of_nonneg_left hsum (screenAccuracy_pos j).le
  simpa using h

theorem positiveThreshold_error (ρ : ℝ) (hρ : 0 < ρ) (j L : ℕ) :
    (∑ k ∈ Finset.range L, Real.exp (-positiveThreshold ρ j k)) ≤ ρ*screenAccuracy j := by
  have he (k : ℕ) : Real.exp (-positiveThreshold ρ j k) = ρ*Real.exp (-negativeThreshold j k) := by
    unfold positiveThreshold
    rw [neg_add,Real.exp_add,Real.exp_neg (Real.log _),Real.exp_log (by positivity)]
    simp [mul_comm]
  simp_rw [he,← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (negativeThreshold_error j L) hρ.le

theorem margin_quadratic (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a : ℝ) (hα : 2 ≤ α) (ha : 0 < a) (hm : PowerMargin μ α a) :
    PowerMargin μ 2 a := by
  intro x hx hxa
  apply (hm x hx hxa).trans
  exact Real.rpow_le_rpow_of_exponent_ge (div_pos hx ha) ((div_le_one ha).2 hxa.le) hα

end ThresholdHC.RareAboveTwo
