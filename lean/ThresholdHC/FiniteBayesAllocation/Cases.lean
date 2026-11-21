import ThresholdHC.FiniteBayesAllocation.Bayes
import ThresholdHC.FiniteBayesAllocation.CertTwo
import ThresholdHC.FiniteBayesAllocation.CertThree

/-! The six certified designs at the two locked cases: the table policy, the
fresh design and the single-coin design, each with its posterior-mean member
(upper bound) and the bound for every estimator with that design (lower
bound). All constants are the specification's roundings at `10^-15`. -/

noncomputable section
namespace ThresholdHC.FiniteBayesAllocation
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.FiniteLawCertificates ThresholdHC.HardBudget

theorem two_tt_le (k : Fin 6) : twoCode.tt k ≤ 2 := by
  fin_cases k <;> decide

theorem three_tt_le (k : Fin 7) : threeCode.tt k ≤ 2 := by
  fin_cases k <;> decide

theorem two_table_lt (u : Fin 8 → Bool) (t : Fin 8) : flipLabel (tableLabel twoScalesTable) u t < 8 :=
  tableLabel_lt _ (by decide +kernel) _

theorem three_table_lt (u : Fin 8 → Bool) (t : Fin 8) :
    flipLabel (tableLabel threeScalesTable) u t < 8 :=
  tableLabel_lt _ (by decide +kernel) _

/-! ### Upper bounds of the posterior-mean members -/

theorem two_table_upper :
    bayesRisk twoScalesLaw twoScalesSign (postEstimator twoCode (tableLabel twoScalesTable)) ≤
      ENNReal.ofReal (2111783001239 / 10^15) :=
  (@design_upper _ _ _ _ _ _ twoValid twoScalesLaw_probability (by norm_num) _ two_table_lt _ _
    two_adaptive_cert).trans (ENNReal.ofReal_le_ofReal (by norm_num [prec]))

theorem two_fresh_upper :
    bayesRisk twoScalesLaw twoScalesSign (postEstimator twoCode (fun xs => xs.length)) ≤
      ENNReal.ofReal (2149143352672 / 10^15) :=
  (@design_upper _ _ _ _ _ _ twoValid twoScalesLaw_probability (by norm_num) _ fresh_label_lt _ _
    two_fresh_cert).trans (ENNReal.ofReal_le_ofReal (by norm_num [prec]))

theorem two_single_upper :
    bayesRisk twoScalesLaw twoScalesSign (postEstimator twoCode (fun _ => 0)) ≤
      ENNReal.ofReal (2145940859277 / 10^15) :=
  (@design_upper _ _ _ _ _ _ twoValid twoScalesLaw_probability (by norm_num) _ single_label_lt _ _
    two_single_cert).trans (ENNReal.ofReal_le_ofReal (by norm_num [prec]))

theorem three_table_upper :
    bayesRisk threeScalesLaw threeScalesSign (postEstimator threeCode (tableLabel threeScalesTable)) ≤
      ENNReal.ofReal (1706729084112 / 10^15) :=
  (@design_upper _ _ _ _ _ _ threeValid threeScalesLaw_probability (by norm_num) _ three_table_lt _ _
    three_adaptive_cert).trans (ENNReal.ofReal_le_ofReal (by norm_num [prec]))

theorem three_fresh_upper :
    bayesRisk threeScalesLaw threeScalesSign (postEstimator threeCode (fun xs => xs.length)) ≤
      ENNReal.ofReal (1797138065872 / 10^15) :=
  (@design_upper _ _ _ _ _ _ threeValid threeScalesLaw_probability (by norm_num) _ fresh_label_lt _ _
    three_fresh_cert).trans (ENNReal.ofReal_le_ofReal (by norm_num [prec]))

theorem three_single_upper :
    bayesRisk threeScalesLaw threeScalesSign (postEstimator threeCode (fun _ => 0)) ≤
      ENNReal.ofReal (1868722055076 / 10^15) :=
  (@design_upper _ _ _ _ _ _ threeValid threeScalesLaw_probability (by norm_num) _ single_label_lt _ _
    three_single_cert).trans (ENNReal.ofReal_le_ofReal (by norm_num [prec]))

/-! ### Lower bounds over every estimator with a fixed design -/

theorem two_fresh_lower {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (hA : FreshDesign A) :
    ENNReal.ofReal (2149143352671 / 10^15) ≤ bayesRisk twoScalesLaw twoScalesSign A :=
  (ENNReal.ofReal_le_ofReal (by norm_num [prec])).trans
    (@design_lower _ _ _ _ _ _ twoValid twoScalesLaw_probability (by norm_num) two_tt_le _
      fresh_label_lt _ _ two_fresh_cert R _ A hA)

theorem two_single_lower {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (hA : SingleDesign A) :
    ENNReal.ofReal (2145940859276 / 10^15) ≤ bayesRisk twoScalesLaw twoScalesSign A :=
  (ENNReal.ofReal_le_ofReal (by norm_num [prec])).trans
    (@design_lower _ _ _ _ _ _ twoValid twoScalesLaw_probability (by norm_num) two_tt_le _
      single_label_lt _ _ two_single_cert R _ A hA)

theorem three_fresh_lower {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (hA : FreshDesign A) :
    ENNReal.ofReal (1797138065871 / 10^15) ≤ bayesRisk threeScalesLaw threeScalesSign A :=
  (ENNReal.ofReal_le_ofReal (by norm_num [prec])).trans
    (@design_lower _ _ _ _ _ _ threeValid threeScalesLaw_probability (by norm_num) three_tt_le _
      fresh_label_lt _ _ three_fresh_cert R _ A hA)

theorem three_single_lower {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (hA : SingleDesign A) :
    ENNReal.ofReal (1868722055075 / 10^15) ≤ bayesRisk threeScalesLaw threeScalesSign A :=
  (ENNReal.ofReal_le_ofReal (by norm_num [prec])).trans
    (@design_lower _ _ _ _ _ _ threeValid threeScalesLaw_probability (by norm_num) three_tt_le _
      single_label_lt _ _ three_single_cert R _ A hA)

end ThresholdHC.FiniteBayesAllocation
