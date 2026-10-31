import ThresholdHC.StoppingProgram.ConePriceRatio
import ThresholdHC.StoppingProgram.PositiveValue

/-! The exact four-prior value identity and an attained positive dual
quadruple with finite information/work ratio. Primal attainment is separate. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap signMean)

theorem strong_four_prior_duality (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) :
    programSquared μ ρ B N = dualValue μ ρ B N ∧
      ∃ Q : FourPriors, Admissible μ ρ Q ∧ dualRatio μ B N Q = programSquared μ ρ B N ∧
        0 < programSquared μ ρ B N ∧ informationRatio μ N Q < ⊤ := by
  have hp := programSquared_pos N μ hρ hρhalf hB
  have hpfin := programSquared_finite μ hρ.le hB.le N
  have hpreal : 0 < (programSquared μ ρ B N).toReal := ENNReal.toReal_pos hp.ne' hpfin.ne
  obtain ⟨Q,α,η,hQ,hα0,hη,hvalue,hprice⟩ := attained_price_multipliers N μ hρ.le hB
  have hα : 0 < α := by
    by_contra hn
    have he : α = 0 := le_antisymm (le_of_not_gt hn) hα0
    rw [he] at hvalue
    nlinarith [mul_nonneg hη hB.le]
  have hsep : 0 < signMean μ Q.high.val-signMean μ Q.low.val := by
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos hα0 (le_of_not_gt hn)
    nlinarith [sq_nonneg α,mul_nonneg hη hB.le]
  have hK := conePrice_ratio_finite μ Q hα hη hprice
  have hkb := conePrice_ratio_real_bound μ Q hα hη hprice
  let K := (informationRatio μ N Q).toReal
  let D := 4+B*K
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  have hD : 0 < D := by dsimp [D]; positivity
  have hquad : α*(signMean μ Q.high.val-signMean μ Q.low.val)-α^2*(1+B*K/4) ≤
      (signMean μ Q.high.val-signMean μ Q.low.val)^2/D := by
    apply (le_div_iff₀ hD).mpr
    have he : (signMean μ Q.high.val-signMean μ Q.low.val)^2-
        (α*(signMean μ Q.high.val-signMean μ Q.low.val)-α^2*(1+B*K/4))*D =
        (signMean μ Q.high.val-signMean μ Q.low.val-α*D/2)^2 := by
      dsimp [D]
      ring
    nlinarith [sq_nonneg (signMean μ Q.high.val-signMean μ Q.low.val-α*D/2)]
  have hreal : (programSquared μ ρ B N).toReal ≤
      (signMean μ Q.high.val-signMean μ Q.low.val)^2/D := by
    have hkB := mul_le_mul_of_nonneg_right hkb hB.le
    change α^2*K*B ≤ 4*η*B at hkB
    nlinarith
  have hden : 4+ENNReal.ofReal B*informationRatio μ N Q = ENNReal.ofReal D := by
    rw [← ENNReal.ofReal_toReal hK,← ENNReal.ofReal_mul hB.le,← ENNReal.ofReal_ofNat 4,
      ← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 4) (mul_nonneg hB.le hK0)]
  have hratio : dualRatio μ B N Q = ENNReal.ofReal ((signMean μ Q.high.val-signMean μ Q.low.val)^2/D) := by
    rw [dualRatio,hden,← ENNReal.ofReal_pow hsep.le,← ENNReal.ofReal_div_of_pos hD]
  have hprimal : programSquared μ ρ B N ≤ dualRatio μ B N Q := by
    rw [hratio,← ENNReal.ofReal_toReal hpfin.ne]
    exact ENNReal.ofReal_le_ofReal hreal
  have hsup : dualRatio μ B N Q ≤ dualValue μ ρ B N :=
    le_iSup_of_le Q (le_iSup_of_le hQ le_rfl)
  have hweak := weak_duality μ (ρ := ρ) hB N
  exact ⟨le_antisymm (hprimal.trans hsup) hweak,
    Q,hQ,le_antisymm (hsup.trans hweak) hprimal,hp,lt_top_iff_ne_top.mpr hK⟩

end ThresholdHC.StoppingProgram
