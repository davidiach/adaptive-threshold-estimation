import ThresholdHC.FiniteQuantileFormula.Formula
import ThresholdHC.FiniteQuantile.Operational

/-! The explicit finite formulas (67)-(69) and Theorem fg:thm:direct-main with that
formula. The lower halves come from the direct finite-law theorem
`FiniteQuantile.direct_finite_law`; the upper minimax half and the single
estimator come from the general-law `28000` upper bound, through
`EntropyTailExecution.closed_quantile_upper_30001` and
`FiniteQuantile.observable_estimator`. The direct finite upper construction of
`paper/v6/finite-upper.tex` is not used. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.FiniteQuantileFormula
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile

theorem finite_formula : FiniteFormulaStatement := by
  intro n d w μ _ hd hw hsum hμ ρ B hρ hρ4 _ N hN
  exact finite_formula_of_le_one d w μ hd hw hsum hμ hρ (by linarith) B hN

theorem explicit_finite_law : ExplicitFiniteLawStatement := by
  intro n d w μ _ hd hw hsum hμ ρ B hρ hρ4 hB N hN
  have hQ := (finite_formula_of_le_one d w μ hd hw hsum hμ hρ (by linarith) B hN).2.2
  have hs : μ.support.Finite := by
    rw [hμ]
    exact atoms_support_finite d w
  have hlow : ENNReal.ofReal ((10:ℝ)⁻¹^20 * finiteQuantile d w ρ B N) =
      ENNReal.ofReal ((10:ℝ)⁻¹^20) * closedQuantileValue μ ρ B := by
    rw [hQ, ENNReal.ofReal_mul (by positivity)]
  have hup : ENNReal.ofReal (30001 * finiteQuantile d w ρ B N) =
      30001 * closedQuantileValue μ ρ B := by
    rw [hQ, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  obtain ⟨h1, h2⟩ := FiniteQuantile.direct_finite_law μ hs ρ B hρ hρ4 hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlow]
    exact h1
  · rw [hup]
    exact h2
  · obtain ⟨S, inst, A, hb, hr⟩ := FiniteQuantile.observable_estimator μ hρ hρ4 hB
    refine ⟨S, inst, A, hb, ?_⟩
    rw [hup]
    exact hr
  · intro S _ A hb
    rw [hlow]
    exact FiniteQuantile.every_estimator_lower μ hs hρ hρ4 hB A hb

end ThresholdHC.FiniteQuantileFormula
