import ThresholdHC.ConfidenceEntropy.Core

noncomputable section
open MeasureTheory Set Real
open scoped BigOperators ENNReal
namespace ThresholdHC.ConfidenceEntropy
open ThresholdHC.FiniteQuantile ThresholdHC.EntropyTailLower ThresholdHC.EntropyTailQuantile
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.RareAboveTwo ThresholdHC.Genie
open ThresholdHC.EntropyTailSharp

theorem closed_quantile_program (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ENNReal.ofReal (30*(10:ℝ)⁻¹^17)*closedQuantileValue μ ρ B ≤ infiniteProgramValue μ ρ B := by
  let t := quantileThreshold μ ρ
  let h := EntropyTailQuantile.budgetScale B
  let T := tailModulus (quantileTail μ ρ) h
  let R := (infiniteProgramValue μ ρ B).toReal
  have hRn : infiniteProgramValue μ ρ B ≠ ⊤ := infiniteProgramValue_ne_top μ hρ.le hB.le
  have hR : 0 ≤ R := ENNReal.toReal_nonneg
  have hrisk := (infinite_program_comparison μ ρ B hρ (by linarith) hB).1
  have hρ1 : ρ ≤ 1 := by linarith
  have htpos : 0 < t := (quantileThreshold_properties μ hρ hρ1).1
  have hh : 0 ≤ h := inv_nonneg.mpr (sqrt_nonneg _)
  have hT : 0 ≤ T := tailModulus_nonneg _ hh
  have htail : T ≤ 32*R := by
    have hl := ENNReal.toReal_mono hRn ((quantile_tail_lower_general μ hρ hρ4 hB).trans hrisk)
    change (ENNReal.ofReal (T/32)).toReal ≤ R at hl
    rw [ENNReal.toReal_ofReal (by positivity)] at hl
    linarith only [hl]
  by_cases hbig : t ≤ h
  · exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (by norm_num : 30*(10:ℝ)⁻¹^17 ≤ 1/32)) le_rfl).trans
      ((above_threshold_lower_general μ hρ hρ4 hB hbig).trans hrisk)
  obtain ⟨n, hn, hbefore⟩ := exists_band_cutoff htpos
  let F := prefixCoreEntropy μ n
  let M := min ρ (sqrt (ρ*F/B))
  have hF : 0 ≤ F := prefixCoreEntropy_nonneg _ _
  have hcore : M ≤ (16*10^14)*R := by
    by_cases hbounded : F ≤ 262144
    · have hroot : sqrt (ρ*F/B) ≤ 512*sqrt (ρ/B) := by
        have hp := mul_le_mul_of_nonneg_left hbounded (div_nonneg hρ.le hB.le)
        have hb : ρ*F/B ≤ 262144*(ρ/B) := by convert hp using 1 <;> ring
        have hle := sqrt_le_sqrt hb
        rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 262144)] at hle
        norm_num at hle
        exact hle
      have hcap := EntropyTailLower.scaled_min_bound ρ (sqrt (ρ/B)) (sqrt (ρ*F/B)) 512
        hρ.le (by norm_num) hroot
      have hl := ENNReal.toReal_mono hRn ((bernoulli_label_minimax_floor μ ρ B hρ hρ4 hB).trans hrisk)
      rw [ENNReal.toReal_ofReal (by positivity)] at hl
      change (1/16)*min ρ (sqrt (ρ/B)) ≤ R at hl
      dsimp only [M]
      nlinarith only [hl, hcap, hR]
    have hFp : 0 < F := by linarith only [hbounded]
    by_cases hcut : 32*(65536*(sqrt ρ/sqrt F)) ≤ t
    · exact core_program_bound μ hρ hρ4 hB htpos hbefore (lt_of_not_ge hbounded) hcut
    have hnear : t*sqrt F ≤ 2097152*sqrt ρ := by
      have hb := (not_le.mp hcut).le
      have he : 32*(65536*(sqrt ρ/sqrt F)) = (2097152*sqrt ρ)/sqrt F := by ring
      rw [he] at hb
      exact (le_div_iff₀ (sqrt_pos.mpr hFp)).mp hb
    have hfloor := quantileTail_threshold_floor μ hρ hρ1 hh (le_of_not_ge hbig)
    change h/t*ρ ≤ T at hfloor
    have hroot : sqrt (ρ*F/B) = h*sqrt ρ*sqrt F := by
      rw [sqrt_div (mul_nonneg hρ.le hF), sqrt_mul hρ.le]
      dsimp [h, EntropyTailQuantile.budgetScale]
      ring
    have hcomp : h*sqrt ρ*sqrt F ≤ 2097152*(h/t*ρ) := by
      have h1 := mul_le_mul_of_nonneg_left hnear (mul_nonneg hh (sqrt_nonneg ρ))
      rw [show 2097152*(h/t*ρ) = (2097152*h*ρ)/t by ring]
      apply (le_div_iff₀ htpos).mpr
      nlinarith only [h1, congrArg (fun x : ℝ => 2097152*h*x) (sq_sqrt hρ.le)]
    have hle : M ≤ h*sqrt ρ*sqrt F := (min_le_right _ _).trans_eq hroot
    linarith only [hle, hcomp, hfloor, htail, hR]
  have hQ := closedQuantile_le_tail_core μ (B := B) hρ.le hn
  change closedQuantileValue μ ρ B ≤ ENNReal.ofReal (T+2*M) at hQ
  calc
    _ ≤ ENNReal.ofReal (30*(10:ℝ)⁻¹^17) * ENNReal.ofReal (T+2*M) := mul_le_mul' le_rfl hQ
    _ = ENNReal.ofReal (30*(10:ℝ)⁻¹^17*(T+2*M)) := (ENNReal.ofReal_mul (by norm_num)).symm
    _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal (by nlinarith only [htail,hcore,hR])
    _ = _ := ENNReal.ofReal_toReal hRn

end ThresholdHC.ConfidenceEntropy
