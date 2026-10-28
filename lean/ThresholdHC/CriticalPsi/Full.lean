import ThresholdHC.CriticalPsi.Specification
import ThresholdHC.CriticalPsi.Separation

noncomputable section
namespace ThresholdHC.CriticalPsi

theorem critical_psi_formula : CriticalPsiFormulaStatement := criticalPsi_formula

theorem critical_psi_rate : CriticalPsiRateStatement := criticalPsi_rate

theorem critical_matching_psi_refuted : CriticalPsiSeparationStatement := critical_psi_separation


end ThresholdHC.CriticalPsi
