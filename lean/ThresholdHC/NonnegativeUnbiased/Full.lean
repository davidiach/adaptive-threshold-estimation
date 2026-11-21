import ThresholdHC.NonnegativeUnbiased.Support

/-! Proposition prop:bounded, first sentence: no nonnegative unbiased output
when some gaps lie below `1/2`. -/
noncomputable section
namespace ThresholdHC.NonnegativeUnbiased

theorem nonnegative_unbiased_impossible : NonnegativeUnbiasedStatement := by
  intro R _ μ _ A hμ hstop hnn
  exact nonnegative_not_unbiased R μ A hμ hstop hnn

end ThresholdHC.NonnegativeUnbiased
