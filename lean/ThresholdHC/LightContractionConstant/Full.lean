import ThresholdHC.LightContractionConstant.Moments

/-! The constant `C_V` of the light random contraction, its band masses and
the inverse moment bounds, stated against the specification. The entropy
inequality `Γ_{L(VD)} ≤ C_V Γ_μ` of (A4)/(UA4) is not part of these targets. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.LightContractionConstant
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.ArbitraryLawAdaptation

theorem first_band_mass : FirstBandStatement := by
  intro ν _ hCDF
  exact bandProb_first ν hCDF

theorem tail_band_mass : TailBandStatement := by
  intro ν _ hCDF k hk
  exact bandProb_tail_ge_three ν hCDF k hk

theorem first_term_bound : FirstTermStatement := by
  intro ν _ _
  exact cvTerm_first_lt ν

theorem light_cv_bound : LightCVStatement := by
  intro ν _ hCDF
  exact ⟨cvTerm_summable ν hCDF, lightCV_lt ν hCDF⟩

theorem light_moment_bounds : LightMomentStatement := by
  intro ν _ hCDF
  exact ⟨inverseSquare_le_lightCV ν hCDF, inverseSquare_le_256 ν hCDF, inverse_le_16 ν hCDF⟩

theorem constructed_light_cv : ConstructedLightCVStatement :=
  ⟨bandProb_first lightMultiplier lightMultiplier_cdf,
    cvTerm_summable lightMultiplier lightMultiplier_cdf,
    lightCV_lt lightMultiplier lightMultiplier_cdf⟩

end ThresholdHC.LightContractionConstant
