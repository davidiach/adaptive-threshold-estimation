import ThresholdHC.QuantileSharpLaw.CountableMerge
import ThresholdHC.EntropyTailQuantile.QuantileComparison

noncomputable section
open MeasureTheory Real Set
open scoped BigOperators ENNReal
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile

theorem measure_prefix_entropy_bound (σ : Measure Gap) (hσ : measureCostEntropy σ ≠ ⊤) (n : ℕ) :
    costEntropy (fun i : Fin n => bandCost σ i.val) ≤ (measureCostEntropy σ).toReal := by
  have h := ENNReal.toReal_mono hσ
    (le_iSup (fun k => ENNReal.ofReal (costEntropy (fun i : Fin k => bandCost σ i.val))) n)
  simpa only [ENNReal.toReal_ofReal (costEntropy_nonneg (fun i : Fin n => bandCost_nonneg σ i.val))] using h

theorem bandCost_summable_of_entropy_finite (σ : Measure Gap) (hσ : measureCostEntropy σ ≠ ⊤) :
    Summable (bandCost σ) :=
  summable_of_prefix_entropy_bound (bandCost_nonneg σ) (measure_prefix_entropy_bound σ hσ)

theorem inverseSquare_lintegral_eq_bandCost (σ : Measure Gap) [IsFiniteMeasure σ] :
    (∫⁻ d : Gap, ENNReal.ofReal ((d : ℝ)⁻¹^2) ∂σ) =
      ∑' j : ℕ, ENNReal.ofReal (bandCost σ j) := by
  conv_lhs => rw [← Measure.restrict_univ (μ := σ),← iUnion_band]
  rw [lintegral_iUnion measurableSet_band bands_disjoint]
  congr 1
  funext j
  exact (ofReal_integral_eq_lintegral_ofReal (band_inverseSquare_integrable σ j)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm

theorem inverseSquare_lintegral_eq_ofReal_tsum (σ : Measure Gap) [IsFiniteMeasure σ]
    (hσ : measureCostEntropy σ ≠ ⊤) :
    (∫⁻ d : Gap, ENNReal.ofReal ((d : ℝ)⁻¹^2) ∂σ) = ENNReal.ofReal (∑' j, bandCost σ j) := by
  rw [inverseSquare_lintegral_eq_bandCost]
  exact (ENNReal.ofReal_tsum_of_nonneg (bandCost_nonneg σ) (bandCost_summable_of_entropy_finite σ hσ)).symm

theorem tailModulus_le_sqrt_bandMoment (σ : Measure Gap) [IsFiniteMeasure σ]
    (hσ : measureCostEntropy σ ≠ ⊤) {ρ h : ℝ} (hρ : 0 ≤ ρ) (hh : 0 ≤ h)
    (hmass : σ univ ≤ ENNReal.ofReal ρ) :
    tailModulus σ h ≤ h*sqrt (ρ*(∑' j, bandCost σ j)) := by
  have hM : 0 ≤ ∑' j, bandCost σ j := tsum_nonneg (bandCost_nonneg σ)
  have hb : ENNReal.ofReal (tailModulus σ h) ≤
      ENNReal.ofReal h*(ENNReal.ofReal ρ*ENNReal.ofReal (∑' j, bandCost σ j))^(1/(2 : ℝ)) := by
    rw [tailModulus,ofReal_integral_eq_lintegral_ofReal (tailKernel_integrable σ hh)
      (Filter.Eventually.of_forall (tailKernel_nonneg hh))]
    calc
      _ ≤ ∫⁻ d : Gap, ENNReal.ofReal h*ENNReal.ofReal ((d : ℝ)⁻¹) ∂σ := by
        apply lintegral_mono
        intro d
        dsimp only
        rw [← ENNReal.ofReal_mul hh]
        apply ENNReal.ofReal_le_ofReal
        simpa only [div_eq_mul_inv] using min_le_right (1 : ℝ) (h/(d : ℝ))
      _ = ENNReal.ofReal h*(∫⁻ d : Gap, ENNReal.ofReal ((d : ℝ)⁻¹) ∂σ) :=
        lintegral_const_mul _ (by fun_prop)
      _ ≤ ENNReal.ofReal h*(σ univ*(∫⁻ d : Gap, ENNReal.ofReal ((d : ℝ)⁻¹^2) ∂σ))^(1/(2 : ℝ)) := by
        gcongr
        exact inverse_lintegral_le_sqrt_moment σ
      _ ≤ _ := by
        rw [inverseSquare_lintegral_eq_ofReal_tsum σ hσ]
        gcongr
  rw [entropy_root_eq_ofReal ENNReal.ofReal_ne_top hρ hh,ENNReal.toReal_ofReal hM] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hh (sqrt_nonneg _))).mp hb

end ThresholdHC.QuantileSharpLaw
