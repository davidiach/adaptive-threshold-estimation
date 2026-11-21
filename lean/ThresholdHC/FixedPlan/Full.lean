import ThresholdHC.FixedPlan.Risk
import ThresholdHC.FixedPlan.Integral

/-! Proofs of the fixed-plan target statements in `Specification.lean`. -/

noncomputable section

namespace ThresholdHC.FixedPlan

theorem majorityWork : MajorityWorkStatement := by
  intro μ _ q k n
  exact majority_expectedWork μ q k n

theorem majorityMissProbability : MajorityMissStatement :=
  majorityVote_error

theorem majorityMean : MajorityMeanStatement := by
  intro μ _ q k n hn
  exact majority_mean μ q k n hn

theorem majorityBias : MajorityBiasStatement := by
  intro μ _ q k n hn
  exact majority_bias μ q k n hn

theorem majorityVariance : MajorityVarianceStatement := by
  intro μ _ q k n hn
  exact majority_evariance μ q k n hn

theorem majorityMSE : MajorityMSEStatement := by
  intro μ _ q k n hn
  exact majority_mse μ q k n hn

theorem majorityRMS : MajorityRMSStatement := by
  intro μ _ k n hn
  exact majority_rms μ k n hn

theorem majorityMinimax : MajorityMinimaxStatement := by
  intro μ _ k n B hn hB
  exact majority_minimax μ k n B hn hB

theorem uniformTailIntegral : UniformTailIntegralStatement :=
  uniform_tail_integral

theorem uniformMeanMiss : UniformMeanMissStatement :=
  uniform_meanMajorityMiss

theorem uniformBeta : UniformBetaStatement :=
  uniform_beta

end ThresholdHC.FixedPlan
