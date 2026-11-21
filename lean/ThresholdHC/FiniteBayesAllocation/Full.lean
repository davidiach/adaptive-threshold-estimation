import ThresholdHC.FiniteBayesAllocation.Cases

/-! Proofs of the target statements of `Specification.lean`. The adaptive
witness is the posterior-mean estimator of the table policy; the restricted
lower bounds hold for every fresh-only or single-coin estimator with any
private seed and any measurable output; the tightness members are the
posterior-mean estimators of the two fixed designs. The gains chain the
witness upper bound with the restricted lower bounds, so they compare an
explicit capped witness with the restricted designs; they do not assert that
the witness is the adaptive Bayes optimum. -/

noncomputable section
namespace ThresholdHC.FiniteBayesAllocation
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.HardBudget

private theorem gain_step (W A : ℝ≥0∞) (U L t : ℝ) (hU : W ≤ ENNReal.ofReal U)
    (hL : ENNReal.ofReal L ≤ A) (ht : 0 ≤ t) (h : U ≤ t * L) : W ≤ ENNReal.ofReal t * A := by
  refine hU.trans ((ENNReal.ofReal_le_ofReal h).trans ?_)
  rw [ENNReal.ofReal_mul ht]
  gcongr

theorem two_scales_upper : TwoScalesUpperStatement :=
  ⟨postEstimator twoCode (tableLabel twoScalesTable), fun _ => rfl, postEstimator_cap _ _,
    two_table_upper⟩

theorem three_scales_upper : ThreeScalesUpperStatement :=
  ⟨postEstimator threeCode (tableLabel threeScalesTable), fun _ => rfl, postEstimator_cap _ _,
    three_table_upper⟩

theorem restricted_lower : RestrictedLowerStatement := by
  intro R _ A
  exact ⟨fun h => ⟨two_fresh_lower A h, three_fresh_lower A h⟩,
    fun h => ⟨two_single_lower A h, three_single_lower A h⟩⟩

theorem two_scales_restricted_tight : TwoScalesRestrictedTightStatement :=
  ⟨⟨postEstimator twoCode (fun xs => xs.length), fun _ => rfl, two_fresh_upper⟩,
    ⟨postEstimator twoCode (fun _ => 0), fun _ => rfl, two_single_upper⟩⟩

theorem three_scales_restricted_tight : ThreeScalesRestrictedTightStatement :=
  ⟨⟨postEstimator threeCode (fun xs => xs.length), fun _ => rfl, three_fresh_upper⟩,
    ⟨postEstimator threeCode (fun _ => 0), fun _ => rfl, three_single_upper⟩⟩

theorem two_scales_pinned_gain : TwoScalesPinnedGainStatement := by
  refine ⟨postEstimator twoCode (tableLabel twoScalesTable), fun _ => rfl, postEstimator_cap _ _, ?_⟩
  intro R _ A hA
  rcases hA with hA | hA
  · exact gain_step _ _ _ _ _ two_table_upper (two_fresh_lower A hA) (by norm_num) (by norm_num)
  · exact gain_step _ _ _ _ _ two_table_upper (two_single_lower A hA) (by norm_num) (by norm_num)

theorem three_scales_pinned_gain : ThreeScalesPinnedGainStatement := by
  refine ⟨postEstimator threeCode (tableLabel threeScalesTable), fun _ => rfl,
    postEstimator_cap _ _, ?_⟩
  intro R _ A hA
  rcases hA with hA | hA
  · exact gain_step _ _ _ _ _ three_table_upper (three_fresh_lower A hA) (by norm_num) (by norm_num)
  · exact gain_step _ _ _ _ _ three_table_upper (three_single_lower A hA) (by norm_num) (by norm_num)

theorem two_scales_gain : TwoScalesGainStatement := by
  obtain ⟨W, hW, -, h⟩ := two_scales_pinned_gain
  exact ⟨W, ⟨_, hW⟩, h⟩

theorem three_scales_gain : ThreeScalesGainStatement := by
  obtain ⟨W, hW, -, h⟩ := three_scales_pinned_gain
  exact ⟨W, ⟨_, hW⟩, h⟩

end ThresholdHC.FiniteBayesAllocation
