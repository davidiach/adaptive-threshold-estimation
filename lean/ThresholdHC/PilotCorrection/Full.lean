import ThresholdHC.PilotCorrection.Saddle
import ThresholdHC.PilotCorrection.Production
import ThresholdHC.PilotCorrection.CoinWitness

/-! Proofs of the restricted pilot-correction targets of `Specification`. -/

noncomputable section
namespace ThresholdHC.PilotCorrection
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- `thm:saddle`. -/
theorem saddle : SaddleStatement := by
  intro Ω _ k π ρ Pplus Pminus _ _ Y Z v hF
  obtain ⟨β₀, q₀, hq₀, hs⟩ := saddle_real hF
  obtain ⟨h1, h2⟩ := saddle_value hq₀ hs
  exact ⟨β₀, q₀, hq₀, hs, h1, h2⟩

/-- The pilot theorem: an independent pilot coefficient cannot beat `F*/n`. -/
theorem pilot_no_gain : PilotNoGainStatement := by
  intro Ω _ k π ρ Pplus Pminus _ _ Y Z v hF
  obtain ⟨β₀, q₀, hq₀, hs⟩ := saddle_real hF
  obtain ⟨h1, _⟩ := saddle_value hq₀ hs
  refine ⟨β₀, variance (fun ω => Y ω - β₀ * Z ω) (coinLaw π Pplus Pminus q₀), h1.symm,
    fun n hn => ⟨fun q hq => integral_rawAverage hF hq β₀ hn, ?_, ?_⟩⟩
  · apply le_antisymm
    · refine iSup₂_le fun q hq => ?_
      rw [fixedRisk_eq hF hq β₀ hn]
      exact ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (hs β₀ (Set.mem_univ _) q hq) (Nat.cast_nonneg n))
    · refine le_iSup₂_of_le q₀ hq₀ ?_
      rw [fixedRisk_eq hF hq₀ β₀ hn]
  · intro T _ L hL βhat hβ
    refine le_iSup₂_of_le q₀ hq₀ ?_
    rw [pilotRisk_eq hF hq₀ hn L hβ]
    have := hL q₀ hq₀
    calc
      ENNReal.ofReal
          (variance (fun ω => Y ω - β₀ * Z ω) (coinLaw π Pplus Pminus q₀) / n) =
          ∫⁻ _, ENNReal.ofReal
            (variance (fun ω => Y ω - β₀ * Z ω) (coinLaw π Pplus Pminus q₀) / n) ∂L q₀ := by
        rw [lintegral_const, measure_univ, mul_one]
      _ ≤ _ := lintegral_mono fun t => ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (hs (βhat t) (Set.mem_univ _) q₀ hq₀) (Nat.cast_nonneg n))

/-- Nonvacuity: a one-gap instance with `F* ≥ ρ(1-ρ) > 0`. -/
theorem coin_witness : CoinWitnessStatement := coinWitness_holds

end ThresholdHC.PilotCorrection
