import ThresholdHC.CriticalPsi.Rate
import ThresholdHC.CriticalEntropy.CriticalMinimax

noncomputable section
namespace ThresholdHC.CriticalPsi
open MeasureTheory Set ThresholdHC.Tier3 ThresholdHC.CriticalEntropy
open ThresholdHC.CriticalUpper
open scoped ENNReal

theorem critical_comparison_budget (ρ L H : ℝ) (hρ : 0 < ρ) (hL : 0 < L) (hH : 0 < H) :
    Real.sqrt (ρ*(L*H)/(L*H/ρ)) = ρ ∧
      (1/Real.sqrt (L*H/ρ))*Real.sqrt (ρ*L) = ρ/Real.sqrt H := by
  constructor
  · have he : ρ*(L*H)/(L*H/ρ) = ρ^2 := by field_simp
    rw [he,Real.sqrt_sq hρ.le]
  · have hr : Real.sqrt ρ ≠ 0 := (Real.sqrt_pos.mpr hρ).ne'
    have hl : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
    have hh : Real.sqrt H ≠ 0 := (Real.sqrt_pos.mpr hH).ne'
    rw [Real.sqrt_div (by positivity : 0 ≤ L*H),Real.sqrt_mul hL.le,
      Real.sqrt_mul hρ.le]
    field_simp
    nlinarith [Real.sq_sqrt hρ.le]

theorem critical_psi_separation :
    ∀ C : ℝ, 0 < C →
      ∃ ρ : unitInterval, 0 < (ρ : ℝ) ∧ (ρ : ℝ) ≤ 1/4 ∧
        ∃ B : ℝ, 1 ≤ B ∧
          ENNReal.ofReal (C*criticalPsi (ρ : ℝ) (1/Real.sqrt B)) <
            criticalMinimaxRisk (ρ : ℝ) B := by
  intro C hC
  obtain ⟨c,hc,hlower⟩ := critical_minimax_lower_bound
  let M := (32*C/c)^2+4
  let x := Real.exp M
  let ρ := Real.exp (-x)
  let L := 1+Real.log (1/ρ)
  let H := 1+Real.log L
  have hM : 4 ≤ M := by dsimp [M]; nlinarith [sq_nonneg (32*C/c)]
  have hx : 0 < x := Real.exp_pos _
  have hx5 : 5 ≤ x := by have he := Real.add_one_le_exp M; dsimp [x]; linarith
  have hρ : 0 < ρ := Real.exp_pos _
  have hρq : ρ ≤ 1/4 := by
    have he := Real.add_one_le_exp x
    dsimp [ρ]
    rw [Real.exp_neg,← one_div]
    apply (div_le_iff₀ (Real.exp_pos x)).mpr
    linarith
  have hLx : L = 1+x := by
    dsimp [L,ρ]
    rw [one_div,Real.log_inv,Real.log_exp]
    ring
  have hL1 : 1 ≤ L := by rw [hLx]; linarith
  have hL : 0 < L := by linarith
  have hH1 : 1 ≤ H := by dsimp [H]; linarith [Real.log_nonneg hL1]
  have hH : 0 < H := by linarith
  have hMH : M < H := by
    have he := Real.log_le_log hx (by linarith : x ≤ 1+x)
    have hex : Real.log x = M := Real.log_exp M
    dsimp [H]
    rw [hLx]
    linarith
  have hcoef : 16*C < c*Real.sqrt H := by
    have hnorm : (32*C/c)^2 < H := by dsimp [M] at hMH; linarith
    have hscale := mul_lt_mul_of_pos_right hnorm (sq_pos_of_pos hc)
    have he : (32*C/c)^2*c^2 = (32*C)^2 := by field_simp
    rw [he] at hscale
    nlinarith [Real.sq_sqrt hH.le,Real.sqrt_nonneg H,
      mul_pos hc (Real.sqrt_pos.mpr hH),sq_nonneg C]
  let B := L*H/ρ
  have hB : 1 ≤ B := by
    apply (le_div_iff₀ hρ).mpr
    have hp := mul_le_mul hL1 hH1 (by norm_num) hL.le
    nlinarith
  have hB0 : 0 < B := by linarith
  let r : unitInterval := ⟨ρ,hρ.le,by linarith⟩
  refine ⟨r,hρ,hρq,B,hB,?_⟩
  have hcal := critical_comparison_budget ρ L H hρ hL hH
  have hF : criticalLogFactor ρ = L*H := rfl
  have hlow := hlower r hρ hρq B hB
  change ENNReal.ofReal (c*min ρ (Real.sqrt (ρ*criticalLogFactor ρ/B))) ≤ _ at hlow
  rw [hF,hcal.1,min_self] at hlow
  have hpsi := (criticalPsi_rate ρ (1/Real.sqrt B) hρ hρq (by positivity)).2
  have hpsi' : criticalPsi ρ (1/Real.sqrt B) ≤ 16*(ρ/Real.sqrt H) := by
    apply hpsi.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 16)
    exact (min_le_right _ _).trans_eq hcal.2
  have hstrict : C*criticalPsi ρ (1/Real.sqrt B) < c*ρ := by
    have hp := mul_le_mul_of_nonneg_left hpsi' hC.le
    have hcoef' : 16*C/Real.sqrt H < c := (div_lt_iff₀ (Real.sqrt_pos.mpr hH)).mpr hcoef
    have hs := mul_lt_mul_of_pos_right hcoef' hρ
    have he : C*(16*(ρ/Real.sqrt H)) = (16*C/Real.sqrt H)*ρ := by ring
    rw [he] at hp
    exact hp.trans_lt hs
  apply lt_of_lt_of_le ?_ hlow
  exact (ENNReal.ofReal_lt_ofReal_iff (mul_pos hc hρ)).mpr hstrict

end ThresholdHC.CriticalPsi
