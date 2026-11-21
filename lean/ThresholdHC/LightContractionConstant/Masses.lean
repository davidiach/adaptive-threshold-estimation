import ThresholdHC.LightContractionConstant.Specification

/-! Band masses `p_k` of the light multiplier: their identification with the
canonical dyadic bands, the range `[0,1]`, the first mass `p_2 = 1 - 2e^{-32}`
and the tail bound `p_k ≤ 2e^{-4^k/2}` for `k ≥ 3`. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.LightContractionConstant
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.EntropyTail

/-- The paper's band `k = j+2` is the canonical band `j+1`. -/
theorem bandProb_band (ν : Measure Gap) (j : ℕ) :
    bandProb ν (j+2) = (ν (band (j+1))).toReal := rfl

theorem bandProb_nonneg (ν : Measure Gap) (k : ℕ) : 0 ≤ bandProb ν k :=
  ENNReal.toReal_nonneg

theorem bandProb_le_one (ν : Measure Gap) [IsProbabilityMeasure ν] (k : ℕ) :
    bandProb ν k ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

theorem bandProb_tail (ν : Measure Gap)
    (hCDF : ∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x))
    (n : ℕ) (hn : 1 ≤ n) : bandProb ν (n+2) ≤ 2 * Real.exp (-((4 : ℝ)^(n+2) / 2)) := by
  rw [bandProb_band]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (lightCDF_band_bound ν hCDF n hn)

theorem bandProb_tail_ge_three (ν : Measure Gap)
    (hCDF : ∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x))
    (k : ℕ) (hk : 3 ≤ k) : bandProb ν k ≤ 2 * Real.exp (-((4 : ℝ)^k / 2)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n+2 := ⟨k-2, by omega⟩
  exact bandProb_tail ν hCDF n (by omega)

theorem two_exp_neg_32_le_one : 2 * Real.exp (-32) ≤ 1 := by
  have h := Real.add_one_le_exp 32
  have hp : 0 < Real.exp 32 := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one hp]
  linarith

theorem bandProb_first (ν : Measure Gap) [IsProbabilityMeasure ν]
    (hCDF : ∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) :
    bandProb ν 2 = 1 - 2 * Real.exp (-32) := by
  have hs : {v : Gap | (1/2 : ℝ)^(2+1) < (v : ℝ) ∧ (v : ℝ) ≤ (1/2 : ℝ)^2} =
      {v : Gap | (v : ℝ) ≤ 1/4} \ {v : Gap | (v : ℝ) ≤ 1/8} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_le]
    norm_num
    tauto
  have hsub : {v : Gap | (v : ℝ) ≤ 1/8} ⊆ {v : Gap | (v : ℝ) ≤ 1/4} := by
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv ⊢
    linarith
  have hm : MeasurableSet {v : Gap | (v : ℝ) ≤ 1/8} :=
    measurableSet_le measurable_subtype_coe measurable_const
  have h4 : lightCDF (1/4) = 1 := by norm_num [lightCDF]
  have h8 : lightCDF (1/8) = 2 * Real.exp (-32) := by norm_num [lightCDF]
  have hle := two_exp_neg_32_le_one
  unfold bandProb
  rw [hs, measure_sdiff hsub hm.nullMeasurableSet (measure_ne_top _ _), hCDF, hCDF, h4, h8,
    ← ENNReal.ofReal_sub _ (by positivity), ENNReal.toReal_ofReal (by linarith)]

end ThresholdHC.LightContractionConstant
