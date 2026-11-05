
import ThresholdHC.AnytimeLower.FiniteCoefficient
import ThresholdHC.AnytimeLower.Quartet
import ThresholdHC.Genie.InfiniteDuality
import ThresholdHC.EntropyTailSharp.Full

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.Genie

/-- Infinite-cap duality supplies a single finite-information certificate
capturing a fixed fraction of the finite asymptotic selection coefficient. -/
theorem coefficient_certificate (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hb : BddAbove (selectionCoefficients μ ρ)) :
    ∃ (Q : FourPriors) (J : ℝ), Admissible μ ρ Q ∧ 0 < J ∧
      infiniteInformationRatio μ Q ≤ ENNReal.ofReal J ∧
      0 < signMean μ Q.high.val-signMean μ Q.low.val ∧
      (((10:ℝ)⁻¹^17)*selectionCoefficient μ ρ/2)^2*J ≤
        (signMean μ Q.high.val-signMean μ Q.low.val)^2 := by
  obtain ⟨B,hB,hBcoef⟩ := exists_coefficient_witness μ hρ (by linarith) hb
  obtain ⟨Q,hQ,he,hpos,hIfin⟩ := infinite_dual_positive_attained μ hρ hρ4 hB
  let Δ := signMean μ Q.high.val-signMean μ Q.low.val
  let I := (infiniteInformationRatio μ Q).toReal
  let J := I+4/B
  let K := (ThresholdHC.EntropyTail.selection μ ρ B).toReal
  let c : ℝ := (10:ℝ)⁻¹^17
  have hΔ : 0 < Δ := by
    by_contra hn
    have hz : ENNReal.ofReal Δ = 0 := ENNReal.ofReal_eq_zero.mpr (not_lt.mp hn)
    have hd : infiniteDualRatio μ B Q = 0 := by
      unfold infiniteDualRatio
      change ENNReal.ofReal Δ ^2 / _ = 0
      rw [hz,zero_pow (by decide),ENNReal.zero_div]
    rw [hd] at he
    exact hpos.ne' he.symm
  have hI : 0 ≤ I := ENNReal.toReal_nonneg
  have hJ : 0 < J := by dsimp [J]; positivity
  have hIe : ENNReal.ofReal I = infiniteInformationRatio μ Q := ENNReal.ofReal_toReal hIfin.ne
  have hIl : infiniteInformationRatio μ Q ≤ ENNReal.ofReal J := by
    rw [← hIe]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (div_nonneg (by norm_num) hB.le))
  have hc : 0 < c := by dsimp [c]; positivity
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hKe : ENNReal.ofReal K = ThresholdHC.EntropyTail.selection μ ρ B :=
    ENNReal.ofReal_toReal (ThresholdHC.HardBudget.finite_selection μ ρ B)
  have hcomp := (ThresholdHC.EntropyTailSharp.paper_comparison μ hρ hρ4 hB).1.trans
    (infinite_program_comparison μ ρ B hρ (by linarith) hB).1
  change ENNReal.ofReal c * ThresholdHC.EntropyTail.selection μ ρ B ≤ infiniteProgramValue μ ρ B at hcomp
  have hp := pow_le_pow_left' hcomp 2
  rw [← he] at hp
  have hden : 0 < 4+B*I := by positivity
  have hde : 4+ENNReal.ofReal B*infiniteInformationRatio μ Q = ENNReal.ofReal (4+B*I) := by
    rw [← hIe,← ENNReal.ofReal_mul hB.le,← ENNReal.ofReal_ofNat 4,
      ← ENNReal.ofReal_add (by norm_num) (mul_nonneg hB.le hI)]
  change (ENNReal.ofReal c * ThresholdHC.EntropyTail.selection μ ρ B)^2 ≤
    (ENNReal.ofReal Δ)^2/(4+ENNReal.ofReal B*infiniteInformationRatio μ Q) at hp
  rw [← hKe,← ENNReal.ofReal_mul hc.le,← ENNReal.ofReal_pow (mul_nonneg hc.le hK),
    hde,← ENNReal.ofReal_pow hΔ.le,← ENNReal.ofReal_div_of_pos hden] at hp
  have hp' : (c*K)^2*(4+B*I) ≤ Δ^2 :=
    (le_div_iff₀ hden).mp ((ENNReal.ofReal_le_ofReal_iff (div_nonneg (sq_nonneg Δ) hden.le)).mp hp)
  have hC := selectionCoefficient_pos μ hρ (by linarith) hb
  have hw := pow_le_pow_left₀ (show 0 ≤ selectionCoefficient μ ρ/2 by positivity) hBcoef.le 2
  change (selectionCoefficient μ ρ/2)^2 ≤ (sqrt B*K)^2 at hw
  rw [mul_pow,sq_sqrt hB.le] at hw
  have hBJ : B*J = 4+B*I := by
    dsimp [J]
    field_simp [hB.ne']
    ring
  have hscaled := mul_le_mul_of_nonneg_right hw (mul_nonneg (sq_nonneg c) hJ.le)
  refine ⟨Q,J,hQ,hJ,hIl,hΔ,?_⟩
  change (c*selectionCoefficient μ ρ/2)^2*J ≤ Δ^2
  rw [← hBJ] at hp'
  calc
    _ = (selectionCoefficient μ ρ/2)^2*(c^2*J) := by ring
    _ ≤ B*K^2*(c^2*J) := hscaled
    _ = (c*K)^2*(B*J) := by ring
    _ ≤ Δ^2 := hp'

end ThresholdHC.AnytimeLower
