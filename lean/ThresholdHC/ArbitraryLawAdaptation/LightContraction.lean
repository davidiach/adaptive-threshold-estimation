import ThresholdHC.ArbitraryLawAdaptation.LightContractionTail
import ThresholdHC.ArbitraryLawAdaptation.SelectionLift

/-! The factor-32 entropy-tail comparison for the specified light multiplier. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

def lightCDF (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if x < 1/4 then 2*Real.exp (-(1/(2*x^2))) else 1

theorem lightCDF_support (ν : Measure Gap) [IsProbabilityMeasure ν]
    (hCDF : ∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) :
    ∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4 := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_le measurable_subtype_coe measurable_const)).mpr
  rw [hCDF]
  norm_num [lightCDF]

theorem lightCDF_band_bound (ν : Measure Gap)
    (hCDF : ∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x))
    (n : ℕ) (hn : 1 ≤ n) : ν (band (n+1)) ≤
      ENNReal.ofReal (2*Real.exp (-((4 : ℝ)^(n+2)/2))) := by
  have hx : (0 : ℝ) < (1/2 : ℝ)^(n+2) := by positivity
  have hu : (1/2 : ℝ)^(n+2) < 1/4 := by
    have hp : (1/2 : ℝ)^(n+2) ≤ (1/2 : ℝ)^3 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    norm_num at hp
    linarith
  have he : 1/(2*((1/2 : ℝ)^(n+2))^2) = (4 : ℝ)^(n+2)/2 := by
    rw [one_div, mul_inv, ← inv_pow, ← inv_pow]
    norm_num
    rw [← pow_mul, Nat.mul_comm (n+2) 2, pow_mul]
    norm_num
    ring
  calc
    _ ≤ ν {v : Gap | (v : ℝ) ≤ (1/2 : ℝ)^(n+2)} :=
      measure_mono (fun v (h : v ∈ band (n+1)) => h.2)
    _ = _ := by rw [hCDF, lightCDF, ite_eq_right (not_le.mpr hx), ite_eq_left hu, he]

theorem lightSelection_le {μ σ : Measure Gap} (ν : Measure Gap) [IsProbabilityMeasure ν]
    (hσ : σ ≤ μ) : (σ.prod ν).map lightGap ≤ (μ.prod ν).map lightGap :=
  Measure.map_mono (Measure.prod_mono hσ le_rfl) measurable_lightGap

theorem lightSelection_residual {μ σ : Measure Gap} [IsFiniteMeasure μ]
    (ν : Measure Gap) [IsProbabilityMeasure ν] (hσ : σ ≤ μ) :
    (μ.prod ν).map lightGap-(σ.prod ν).map lightGap = ((μ-σ).prod ν).map lightGap := by
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le μ hσ
  have he : ((μ-σ).prod ν).map lightGap+(σ.prod ν).map lightGap = (μ.prod ν).map lightGap := by
    rw [← Measure.map_add _ _ measurable_lightGap, ← Measure.add_prod, Measure.sub_add_cancel_of_le hσ]
  rw [← he, Measure.add_sub_cancel]

theorem lightSelection_objective {μ σ : Measure Gap} [IsFiniteMeasure μ]
    (ν : Measure Gap) [IsProbabilityMeasure ν] (hσ : σ ≤ μ)
    (hv : ∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4)
    (hp : ∀ n : ℕ, 1 ≤ n → ν (band (n+1)) ≤
      ENNReal.ofReal (2*Real.exp (-((4 : ℝ)^(n+2)/2)))) (ρ B : ℝ) :
    selectionObjective ((μ.prod ν).map lightGap) ρ B ((σ.prod ν).map lightGap) ≤
      32*selectionObjective μ ρ B σ := by
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le μ hσ
  have hg := gamma_light_contraction σ ν hv hp
  have ht := tailCost_light_contraction (μ-σ) ν hv hp (h := 1/Real.sqrt B) (by positivity)
  have hroot : (1024 : ℝ≥0∞)^(1/2 : ℝ) = 32 := by
    rw [← ENNReal.ofReal_ofNat, ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num),
      ← Real.sqrt_eq_rpow]
    norm_num
  unfold selectionObjective
  rw [mul_add, lightSelection_residual ν hσ]
  apply add_le_add _ ht
  calc
    _ ≤ ENNReal.ofReal (1/Real.sqrt B)*(ENNReal.ofReal ρ*(1024*gamma σ))^(1/2 : ℝ) :=
      mul_le_mul_right (ENNReal.rpow_le_rpow (mul_le_mul_right hg _) (by norm_num)) _
    _ = _ := by
      rw [mul_left_comm (ENNReal.ofReal ρ), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hroot]
      ac_rfl

theorem selection_light_contraction_of_bands (μ ν : Measure Gap)
    [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hv : ∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4)
    (hp : ∀ n : ℕ, 1 ≤ n → ν (band (n+1)) ≤
      ENNReal.ofReal (2*Real.exp (-((4 : ℝ)^(n+2)/2)))) (ρ B : ℝ) :
    selection ((μ.prod ν).map lightGap) ρ B ≤ 32*selection μ ρ B := by
  conv_rhs => rw [selection, mul_min]
  apply le_min
  · exact (selection_le_rho _ _ _).trans (by
      simpa only [one_mul] using mul_le_mul_left (by norm_num : (1 : ℝ≥0∞) ≤ 32) (ENNReal.ofReal ρ))
  · rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
    refine le_iInf fun σ => ?_
    rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
    refine le_iInf fun hσ => ?_
    exact (selection_le_objective (lightSelection_le ν hσ) ρ B).trans
      (lightSelection_objective ν hσ hv hp ρ B)

/-- A3 for exactly the multiplier distribution specified in the paper.
Independence is realized by the product measure, and every fractional
selection is transported. No moment condition is imposed on the gap law. -/
theorem selection_light_contraction (μ ν : Measure Gap)
    [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hCDF : ∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) (ρ B : ℝ) :
    selection ((μ.prod ν).map lightGap) ρ B ≤ 32*selection μ ρ B :=
  selection_light_contraction_of_bands μ ν (lightCDF_support ν hCDF) (lightCDF_band_bound ν hCDF) ρ B

end ThresholdHC.ArbitraryLawAdaptation
