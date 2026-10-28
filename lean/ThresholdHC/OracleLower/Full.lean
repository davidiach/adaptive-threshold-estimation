import ThresholdHC.OracleLower.RMS
import ThresholdHC.OracleLower.Confidence
import ThresholdHC.OracleLower.SelectedSemantics
import ThresholdHC.OracleLower.Nonvacuity

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.OracleLower
open ThresholdHC.Tier6 ThresholdHC.Confidence

theorem revealed_lower_bounds : RevealedLowerStatement := by
  intro R _ μ _ A B hB hb
  exact ⟨oracle_rms_lower (PopulationSeed R) μ (revealedOracle μ A) B hB hb,
    fun δ r hδ hδle hr hc => oracle_confidence_lower (PopulationSeed R) μ
      (revealedOracle μ A) B δ r hB hδ hδle hr hb hc⟩

theorem selected_lower_bounds : SelectedLowerStatement := by
  intro R _ μ _ A B hB hb
  exact ⟨oracle_rms_lower R μ (selectedOracle A) B hB hb,
    fun δ r hδ hδle hr hc => oracle_confidence_lower R μ
      (selectedOracle A) B δ r hB hδ hδle hr hb hc⟩

theorem oracle_minimax_lower : OracleMinimaxLowerStatement := by
  intro μ _ B δ hB hδ hδle
  refine ⟨?_,?_,?_,?_⟩
  · apply le_sInf
    rintro t ⟨R,mR,A,hb,rfl⟩
    exact (revealed_lower_bounds R μ A B hB hb).1
  · apply le_sInf
    rintro t ⟨R,mR,A,hb,rfl⟩
    exact (selected_lower_bounds R μ A B hB hb).1
  · apply le_sInf
    rintro t ⟨R,mR,A,r,hr,hb,hc,rfl⟩
    exact ENNReal.ofReal_le_ofReal ((revealed_lower_bounds R μ A B hB hb).2 δ r hδ hδle hr hc)
  · apply le_sInf
    rintro t ⟨R,mR,A,r,hr,hb,hc,rfl⟩
    exact ENNReal.ofReal_le_ofReal ((selected_lower_bounds R μ A B hB hb).2 δ r hδ hδle hr hc)

end ThresholdHC.OracleLower
