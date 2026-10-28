import ThresholdHC.OracleLower.Information

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.OracleLower
open ThresholdHC.Tier6

theorem oracle_rms_lower : OracleRMSLowerStatement := by
  intro R _ μ _ A B hB hbudget
  let h := budgetScale B
  have hh : 0 < h := (budget_hard_pair μ B hB).1
  have hv := hard_pair_validity h hh
  let qp : SignLaw := ⟨hardPlus h,hv.2.1,fun d => (hv.2.2.2 d).2.2.1⟩
  let qm : SignLaw := ⟨hardMinus h,hv.2.2.1,fun d => (hv.2.2.2 d).2.2.2⟩
  let P := oracleLaw A qp
  let Q := oracleLaw A qm
  let a := signMean μ qp.val
  let b := signMean μ qm.val
  have hk := oracle_hard_pair_information A B h hh hbudget
  change klDiv P Q ≤ _ at hk
  have hkl : klDiv P Q ≤ ENNReal.ofReal (1/8:ℝ) := by
    apply hk.trans
    apply ENNReal.ofReal_le_ofReal
    have hs : h^2*B = 1/16 := (budget_hard_pair μ B hB).2.1
    nlinarith
  have hsep : a-b = (1/4:ℝ)*modulus μ h := hard_pair_separation μ h hh
  have hgap : 0 < a-b := by rw [hsep]; exact mul_pos (by norm_num) (modulus_pos μ hh)
  have hne : a ≠ b := by intro he; rw [he,sub_self] at hgap; exact lt_irrefl _ hgap
  have hsq := two_point_risk_lower_of_ne P Q A.output a b A.output_measurable hne hkl
  have hsquared : ENNReal.ofReal ((a-b)^2/16) ≤
      max (squaredRisk P A.output a) (squaredRisk Q A.output b) := by
    convert hsq using 1; congr 1; ring
  have hrms := rms_of_squared_lower P Q A.output a b (a-b) hgap.le hsquared
  have hscale : modulus μ (1/Real.sqrt B)/16 ≤ a-b := (budget_hard_pair μ B hB).2.2
  calc
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/64) ≤ ENNReal.ofReal ((a-b)/4) :=
      ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ max (rootMeanRisk P A.output a) (rootMeanRisk Q A.output b) := hrms
    _ ≤ oracleRisk μ A := max_le
      (le_iSup (fun q : SignLaw => rootMeanRisk (oracleLaw A q) A.output (signMean μ q.val)) qp)
      (le_iSup (fun q : SignLaw => rootMeanRisk (oracleLaw A q) A.output (signMean μ q.val)) qm)

end ThresholdHC.OracleLower
