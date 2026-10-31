import ThresholdHC.CapIdentification.DiameterAttainment

/-! Support characterization and primal lower bound for the attained
moment-matching diameter. The infinite-budget upper limit is separate. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram

theorem capDiameter_zero_iff_target (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 ≤ ρ) (N : ℕ) : capDiameter μ ρ N = 0 ↔ CapDeterminesTarget μ ρ N := by
  obtain ⟨qH,qL,hH,hL,hm,he,hmax⟩ := capDiameter_attained μ hρ N
  constructor
  · intro hz rH rL hrH hrL hrm
    have hforward := hmax rH rL hrH hrL ((odd_moments_iff_count_match μ rH rL N).mpr hrm)
    have hreverse := hmax rL rH hrL hrH ((odd_moments_iff_count_match μ rL rH N).mpr
      (fun s => (hrm s).symm))
    rw [hz] at hforward hreverse
    linarith
  · intro ht
    rw [he,ht qH qL hH hL ((odd_moments_iff_count_match μ qH qL N).mp hm),sub_self]

theorem finite_support_diameter_zero_iff (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ)
    (S : Finset Gap) (hS : μ.support = (S:Set Gap)) (hcard : 0 < S.card) :
    capDiameter μ ρ N = 0 ↔ 2*S.card-1 ≤ N :=
  (capDiameter_zero_iff_target μ hρ.le N).trans
    (finite_support_target_threshold μ ρ hρ hρ1 N S hS hcard)

theorem infinite_support_diameter_pos (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hμ : μ.support.Infinite) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ) :
    0 < capDiameter μ ρ N := by
  have hn : capDiameter μ ρ N ≠ 0 := by
    intro hz
    exact infinite_support_target_not_identified μ hμ ρ hρ hρ1 N
      ((capDiameter_zero_iff_target μ hρ.le N).mp hz)
  exact lt_of_le_of_ne (capDiameter_bounds μ hρ.le N).1 hn.symm

theorem capDiameter_program_floor (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 ≤ ρ) (B : ℝ) (N : ℕ) :
    ENNReal.ofReal ((capDiameter μ ρ N/2)^2) ≤ programSquared μ ρ B N := by
  obtain ⟨qH,qL,hH,hL,hm,he,_⟩ := capDiameter_attained μ hρ N
  rw [he]
  exact matching_pair_program_floor μ ρ B N qH qL hH hL hm

theorem oddMomentMatch_mono (μ : Measure Gap) (qH qL : SignLaw)
    {M N : ℕ} (hMN : M ≤ N) (h : OddMomentMatch μ qH qL N) : OddMomentMatch μ qH qL M := by
  intro j
  exact h ⟨j.val,by have hj := j.isLt; omega⟩

theorem capDiameter_antitone (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 ≤ ρ) : Antitone (capDiameter μ ρ) := by
  intro M N hMN
  obtain ⟨qH,qL,hH,hL,hm,he,_⟩ := capDiameter_attained μ hρ N
  obtain ⟨_,_,_,_,_,_,hmax⟩ := capDiameter_attained μ hρ M
  rw [he]
  exact hmax qH qL hH hL (oddMomentMatch_mono μ qH qL hMN hm)

end ThresholdHC.CapIdentification
