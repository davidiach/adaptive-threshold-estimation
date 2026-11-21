import ThresholdHC.UpperTwelveNumerics.CallCost
import ThresholdHC.UpperTwelveNumerics.WrongSide
import ThresholdHC.UpperTwelveNumerics.SecondMoment
import ThresholdHC.UpperTwelveNumerics.Remarks

/-! The decimal bounds and the remarks of the appendix on the upper constant 12
(`paper/v6/appendix-upper-constant.tex`, `app:upper-12`), one theorem per
target of `Specification`. -/
noncomputable section
namespace ThresholdHC.UpperTwelveNumerics
open MeasureTheory ThresholdHC.Tier6

/-- `(1-r)∑_{j≥1} r^j C_j sqrt v_j < 5.19`. -/
theorem call_cost_decimal : CallCostDecimalStatement :=
  ⟨callCost_summable, lt_of_le_of_lt callCost_tsum_le (by norm_num)⟩

/-- The wrong-side early stops: `< 0.401`. -/
theorem wrong_side_decimal : WrongSideDecimalStatement :=
  ⟨wrongSideConstant_lt, fun _ _ hd => wrongSide_levelSum_le _ hd⟩

/-- The one-call second moment: `(2+sqrt 2)*89/50 + 41/100 < 6.49`. -/
theorem second_moment_decimal : SecondMomentDecimalStatement :=
  ⟨secondMoment_expr_lt, fun L d S hd hdmax => secondMoment_d_le L d S hd hdmax⟩

/-- The two-level mixture pays `9/2`: `sqrt((9/2)*174/5) ≈ 12.5`. -/
theorem mixture_remark : MixtureRemarkStatement :=
  ⟨mixture_constant_bounds.1, mixture_constant_bounds.2, fun B hB μ _ =>
    ⟨UpperMixture.budgetMixture_uniformBudget B μ, budgetMixture_risk_call B hB μ⟩⟩

/-- The dyadic batch pays the factor `B/2^L < 8`, with supremum `8`, and the family
`budgetEstimator B` keeps the budget `B` with RMS risk at most `sqrt(8*174/5)*ω`. -/
theorem dyadic_batch : DyadicBatchStatement :=
  ⟨dyadic_ratio_lt, dyadic_ratio_sup, fun B hB μ _ =>
    ⟨BlindUpper.budgetEstimator_uniformBudget B μ, budgetEstimator_risk_call B hB μ⟩⟩

/-- At scale `B/4` the squared bias of the level-`L` call is at most
`λ*ω((B/4)^{-1/2})^2`, `1 ≤ λ < 2`, and `ω((B/4)^{-1/2})^2 ≤ 4*ω(B^{-1/2})^2`. -/
theorem scale_four_bias : ScaleFourBiasStatement :=
  fun B hB μ _ q => scaleFour_bias B hB μ q

end ThresholdHC.UpperTwelveNumerics
