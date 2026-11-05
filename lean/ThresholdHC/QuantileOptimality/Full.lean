import ThresholdHC.QuantileOptimality.Witness

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.QuantileOptimality
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile ThresholdHC.OptimalQuantile

theorem finite_sharpness : FiniteSharpnessStatement := by
  intro k hk
  have hroot : 1 < scalarRoot :=
    (one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans_lt scalarRoot_interior.1
  have hl : max 1 k < scalarRoot := max_lt hroot hk
  obtain ⟨m,x,hx,hprice⟩ := finite_vector_witness_below_root hl
  obtain ⟨μ,hμ,hfinite,ρ,B,hρ,hρ4,hB,hstrict⟩ :=
    finite_law_witness x hx (show 0 ≤ max 1 k by positivity) hprice
  refine ⟨μ,hμ,hfinite,ρ,B,hρ,hρ4,hB,?_⟩
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right 1 k)) le_rfl).trans_lt hstrict

theorem universalFactor_iff (k : ℝ) : UniversalFactor k ↔ scalarRoot ≤ k := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨μ,hμ,_,ρ,B,hρ,hρ4,hB,hstrict⟩ := finite_sharpness k (lt_of_not_ge hn)
    have : IsProbabilityMeasure μ := hμ
    exact (not_lt_of_ge (h μ ρ B hρ hρ4 hB)) hstrict
  · intro hk μ _ ρ B hρ hρ4 hB
    have h := (ThresholdHC.QuantileSharpLaw.locked_sharp_quantile_comparison μ hρ hρ4 hB).2
    exact h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hk) le_rfl)

theorem finiteUniversalFactor_iff (k : ℝ) : FiniteUniversalFactor k ↔ scalarRoot ≤ k := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨μ,hμ,hfinite,ρ,B,hρ,hρ4,hB,hstrict⟩ := finite_sharpness k (lt_of_not_ge hn)
    have : IsProbabilityMeasure μ := hμ
    exact (not_lt_of_ge (h μ hfinite ρ B hρ hρ4 hB)) hstrict
  · intro hk μ _ _ ρ B hρ hρ4 hB
    exact (universalFactor_iff k).mpr hk μ ρ B hρ hρ4 hB

theorem general_and_finite_factors_iff (k : ℝ) : UniversalFactor k ↔ FiniteUniversalFactor k :=
  (universalFactor_iff k).trans (finiteUniversalFactor_iff k).symm

end ThresholdHC.QuantileOptimality
