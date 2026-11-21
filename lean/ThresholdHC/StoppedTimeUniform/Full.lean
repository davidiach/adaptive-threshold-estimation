import ThresholdHC.StoppedTimeUniform.Prefix

/-! The fixed-budget coefficient for prefix estimates and the time-uniform
remark. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppedTimeUniform
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.AnytimeLower

theorem prefix_confidence : PrefixConfidenceStatement := by
  intro R _ μ _ ρ δ ε n hρ hρ4 hδ hδ4 hε hn A H hH hc
  exact prefix_confidence_explicit μ A H hH hρ hρ4 hn hδ hδ4 hε hc

theorem stopped_fixed_budget : StoppedFixedBudgetStatement := by
  intro R _ μ _ ρ δ hρ hρ4 hδ hδ4 A L U hL hU t ht hc n hn
  have h := prefix_confidence_explicit μ A (fun x => (L n x + U n x)/2)
    ((hL n).add (hU n) |>.div_const 2) hρ hρ4 hn hδ hδ4 (ht n)
    (coverage_prefix_failure μ A L U hL hU t hc n)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (ht n),
    ENNReal.toReal_ofReal (show 0 ≤ (10:ℝ)⁻¹^17 by positivity)] using hr

theorem stopped_time_uniform : StoppedTimeUniformStatement := by
  intro R _ μ _ ρ δ hρ hρ4 hδ hδ4 A L U hL hU t ht hc n hn hlog
  have hfixed := stopped_fixed_budget R μ ρ δ hρ hρ4 hδ hδ4 A L U hL hU t ht hc n (by omega)
  have hsel := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ThresholdHC.HardBudget.finite_selection μ ρ _))
    (inflation_selection (μ := μ) (ρ := ρ) hδ hδ4 hn hlog)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hsel
  calc (10 : ℝ)⁻¹ ^ 22 *
        (ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ)/budgetInflation δ n)).toReal
      ≤ (10 : ℝ)⁻¹ ^ 22 * ((10 : ℝ) ^ 5 *
          (ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ)/Real.log (1/δ))).toReal) := by
        gcongr
    _ = (10 : ℝ)⁻¹ ^ 17 *
          (ThresholdHC.EntropyTail.selection μ ρ ((n : ℝ)/Real.log (1/δ))).toReal := by
        ring
    _ ≤ t n := hfixed

end ThresholdHC.StoppedTimeUniform
