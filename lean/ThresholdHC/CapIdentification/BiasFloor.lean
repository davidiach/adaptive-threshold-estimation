import ThresholdHC.CapIdentification.CountMatching

/-! Every feasible finite-cap certificate pays at least half the target
gap of a moment-matching pair. This proves the floor direction directly
from the primal program, without invoking four-prior duality. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo
open ThresholdHC.StoppingProgram

theorem matching_target_gap_le_twice_bias {N : ℕ} (μ : Measure Gap) [IsFiniteMeasure μ]
    {ρ B : ℝ} (C : Certificate N) (hC : Feasible μ ρ B C) (qH qL : SignLaw)
    (hH : RarePrior μ ρ qH) (hL : RarePrior μ ρ qL) (hmatch : OddMomentMatch μ qH qL N) :
    |signMean μ qH.val-signMean μ qL.val| ≤ 2*C.bias := by
  have hm := countMean_eq_of_count_match μ qH qL
    ((odd_moments_iff_count_match μ qH qL N).mp hmatch) C.flow.outputWeight
  have h1 := abs_le.mp (hC.bias_bound qH hH)
  have h2 := abs_le.mp (hC.bias_bound qL hL)
  rw [hm] at h1
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem matching_pair_certificate_floor {N : ℕ} (μ : Measure Gap) [IsFiniteMeasure μ]
    {ρ B : ℝ} (C : Certificate N) (hC : Feasible μ ρ B C) (qH qL : SignLaw)
    (hH : RarePrior μ ρ qH) (hL : RarePrior μ ρ qL) (hmatch : OddMomentMatch μ qH qL N) :
    ENNReal.ofReal (((signMean μ qH.val-signMean μ qL.val)/2)^2) ≤ certificateSquared C := by
  have h := matching_target_gap_le_twice_bias μ C hC qH qL hH hL hmatch
  have habs : 0 ≤ |signMean μ qH.val-signMean μ qL.val| := abs_nonneg _
  have hs := sq_abs (signMean μ qH.val-signMean μ qL.val)
  unfold certificateSquared
  apply ENNReal.ofReal_le_ofReal
  nlinarith [hC.bias_nonneg,hC.variance_nonneg,sq_nonneg
    (C.bias-|signMean μ qH.val-signMean μ qL.val|/2)]

theorem matching_pair_program_floor (μ : Measure Gap) [IsFiniteMeasure μ]
    (ρ B : ℝ) (N : ℕ) (qH qL : SignLaw)
    (hH : RarePrior μ ρ qH) (hL : RarePrior μ ρ qL) (hmatch : OddMomentMatch μ qH qL N) :
    ENNReal.ofReal (((signMean μ qH.val-signMean μ qL.val)/2)^2) ≤ programSquared μ ρ B N := by
  apply le_sInf
  rintro x ⟨C,hC,rfl⟩
  exact matching_pair_certificate_floor μ C hC qH qL hH hL hmatch

end ThresholdHC.CapIdentification
