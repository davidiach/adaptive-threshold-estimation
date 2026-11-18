import ThresholdHC.SharpRMS.OracleReduction
import ThresholdHC.SharpRMS.Unrestricted

/-! The unrestricted lower bounds also hold with revealed or adaptively chosen magnitudes. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory Tier6 OracleLower
open scoped ENNReal

private def cappedGap (h : ℝ) (hp : 0 < h) : Gap := ⟨min (1/2) h,lt_min (by norm_num) hp,min_le_left ..⟩

private theorem capped_modulus (μ : Measure Gap) (h : ℝ) (hp : 0<h) :
    modulus μ (cappedGap h hp).val = modulus μ h := by
  unfold modulus
  apply integral_congr_ae
  apply ae_of_all
  intro d
  by_cases hh : h ≤ 1/2
  · simp only [cappedGap,min_eq_right hh]
  · have h0 : 1 ≤ (1/2)/d.val := (one_le_div d.property.1).2 d.property.2
    have h1 : 1 ≤ h/d.val := (one_le_div d.property.1).2 (d.property.2.trans (le_of_not_ge hh))
    simp only [cappedGap,clippedGap,min_eq_left (le_of_not_ge hh),min_eq_left h0,min_eq_left h1]

private theorem capped_dirac (h : ℝ) (hp : 0<h) :
    modulus (Measure.dirac (cappedGap h hp)) h=1 := by
  simp only [modulus,integral_dirac,clippedGap]
  exact min_eq_left ((one_le_div (cappedGap h hp).property.1).2 (min_le_right ..))

private theorem lift_lower (μ : Measure Gap) [IsProbabilityMeasure μ] (B h c : ℝ) (hp : 0<h)
    (low : ∀ g : Gap, ENNReal.ofReal (modulus (Measure.dirac g) h*c) ≤ minimaxRisk (Measure.dirac g) B) :
    ENNReal.ofReal (modulus μ h*c) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ h*c) ≤ selectedMinimaxRisk μ B := by
  let g := cappedGap h hp
  have crit : ENNReal.ofReal c ≤ minimaxRisk (Measure.dirac g) B := by
    simpa only [g,capped_dirac,one_mul] using low g
  have all (R : Type) [MeasurableSpace R] (A : OracleEstimator R) (hb : OracleBudget A B) :
      ENNReal.ofReal (modulus μ h*c) ≤ oracleRisk μ A := by
    rw [←capped_modulus μ h hp,ENNReal.ofReal_mul (modulus_pos μ g.property.1).le]
    exact (mul_le_mul_right crit _).trans (oracle_gap_reduction μ g A B hb)
  constructor
  · apply le_sInf
    rintro x ⟨R,mR,A,hb,rfl⟩
    exact all _ (revealedOracle μ A) hb
  · apply le_sInf
    rintro x ⟨R,mR,A,hb,rfl⟩
    exact all R (selectedOracle A) hb

theorem oracle_minimax_lower (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) (hb : 1 ≤ B) :
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/6) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/6) ≤ selectedMinimaxRisk μ B := by
  simpa only [div_eq_mul_inv,one_mul] using lift_lower μ B (1/Real.sqrt B) (1/6) (by positivity)
    (fun g => by simpa only [div_eq_mul_inv,one_mul] using unrestricted_minimax_lower (Measure.dirac g) B hb)

theorem oracle_large_budget_lower (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) (hb : 25 ≤ B) :
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*Real.sqrt (59/2100:ℝ)) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*Real.sqrt (59/2100:ℝ)) ≤ selectedMinimaxRisk μ B :=
  lift_lower μ B _ _ (by positivity) (fun g => large_budget_minimax_lower (Measure.dirac g) B hb)

end ThresholdHC.SharpRMS
