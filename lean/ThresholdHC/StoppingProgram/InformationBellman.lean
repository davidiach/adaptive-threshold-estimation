import ThresholdHC.StoppingProgram.BellmanFlow
import ThresholdHC.StoppingProgram.PrefixInformation
import ThresholdHC.StoppingProgram.PriceRatio

/-! The actual four-prior information/work ratio is attained by the
deterministic Bellman count policy whenever the prefix rewards are finite. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap)

theorem treeInformation_nonneg (r : ℕ → ℕ → ℝ) (hr : ∀ n k, 0 ≤ r n k)
    (d n k : ℕ) (a : StopTree d) : 0 ≤ treeInformation r d n k a := by
  induction d generalizing n k with
  | zero => exact hr n k
  | succ d ih =>
    cases a with
    | none => exact hr n k
    | some a => exact add_nonneg (ih _ _ a.1) (ih _ _ a.2)

def bellmanRatio (μ : Measure Gap) (N : ℕ) (Q : FourPriors) : ℝ :=
  ratioValue (rootInformation (prefixReward μ Q) (N-1))
    (rootWork (prefixCoefficient μ Q.work) (N-1))

theorem bellmanRatio_nonneg (μ : Measure Gap) (N : ℕ) (Q : FourPriors) :
    0 ≤ bellmanRatio μ N Q := by
  apply ratioValue_nonneg
  · intro a
    exact add_nonneg (treeInformation_nonneg _ (fun _ _ => ENNReal.toReal_nonneg) _ _ _ _)
      (treeInformation_nonneg _ (fun _ _ => ENNReal.toReal_nonneg) _ _ _ _)
  · intro a
    unfold rootWork
    positivity [treeWork_nonneg _ (prefixCoefficient_nonneg μ Q.work) (N-1) 1 0 a.1,
      treeWork_nonneg _ (prefixCoefficient_nonneg μ Q.work) (N-1) 1 1 a.2]

theorem flowScore_information {N : ℕ} (μ : Measure Gap) (Q : FourPriors)
    (f : Flow N) (hf : FlowCone f) (κ : ℝ)
    (hfin : ∀ n k, n ≤ N → k ≤ n → prefixInformation μ Q n k ≠ ⊤) :
    rawFlowScore f (prefixReward μ Q) (prefixCoefficient μ Q.work) κ =
      (flowInformation μ Q f).toReal-κ*countMean μ Q.work f.continueWeight := by
  rw [flowInformation_toReal_raw μ Q f hf hfin,← rawLayer_countMean]
  unfold rawFlowScore rawLayer
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem informationRatio_le_bellmanRatio (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : FourPriors)
    (hfin : ∀ n k, n ≤ N → k ≤ n → prefixInformation μ Q n k ≠ ⊤) :
    informationRatio μ N Q ≤ ENNReal.ofReal (bellmanRatio μ N Q) := by
  have hzero : rootBellman (prefixReward μ Q) (prefixCoefficient μ Q.work)
      (bellmanRatio μ N Q) (N-1) = 0 :=
    (rootBellman_zero_iff _ _ (prefixCoefficient_nonneg μ Q.work) _ _).mpr rfl
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  apply iSup_le
  intro hi
  have hs := flowScore_le_rootBellman f hf (prefixReward μ Q) (prefixCoefficient μ Q.work)
    (bellmanRatio μ N Q) (prefixCoefficient_root μ Q.work)
  rw [flowScore_information μ Q f hf _ hfin,hzero,mul_zero,sub_nonpos] at hs
  have hw : 0 < countMean μ Q.work f.continueWeight := by
    have h := flow_work_ge_intensity μ Q.work f hf
    rw [hi] at h
    linarith
  apply (ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr hw) ENNReal.ofReal_ne_top).mpr
  rw [← ENNReal.ofReal_toReal (flowInformation_finite_prefixes μ Q f hfin),
    ← ENNReal.ofReal_mul (bellmanRatio_nonneg μ N Q)]
  exact ENNReal.ofReal_le_ofReal hs

theorem informationRatio_bellman_attained (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : FourPriors) (hN : 0 < N)
    (hfin : ∀ n k, n ≤ N → k ≤ n → prefixInformation μ Q n k ≠ ⊤) :
    informationRatio μ N Q = ENNReal.ofReal (bellmanRatio μ N Q) ∧
    let f := bellmanFlow (prefixReward μ Q) (prefixCoefficient μ Q.work) (bellmanRatio μ N Q) N
    FlowCone f ∧ intensity f = 1 ∧
      flowInformation μ Q f/ENNReal.ofReal (countMean μ Q.work f.continueWeight) = informationRatio μ N Q := by
  let f := bellmanFlow (prefixReward μ Q) (prefixCoefficient μ Q.work) (bellmanRatio μ N Q) N
  have hf : FlowCone f := bellmanFlow_cone _ _ _ hN
  have hi : intensity f = 1 := bellmanFlow_intensity _ _ _ _
  have hzero : rootBellman (prefixReward μ Q) (prefixCoefficient μ Q.work)
      (bellmanRatio μ N Q) (N-1) = 0 :=
    (rootBellman_zero_iff _ _ (prefixCoefficient_nonneg μ Q.work) _ _).mpr rfl
  have hs := bellmanFlow_score (prefixReward μ Q) (prefixCoefficient μ Q.work) (bellmanRatio μ N Q)
    hN (prefixCoefficient_root μ Q.work)
  change rawFlowScore f _ _ _ = _ at hs
  rw [flowScore_information μ Q f hf _ hfin,hzero,sub_eq_zero] at hs
  have hw : 0 < countMean μ Q.work f.continueWeight := by
    have h := flow_work_ge_intensity μ Q.work f hf
    rw [hi] at h
    linarith
  have hr : flowInformation μ Q f/ENNReal.ofReal (countMean μ Q.work f.continueWeight) =
      ENNReal.ofReal (bellmanRatio μ N Q) := by
    rw [← ENNReal.ofReal_toReal (flowInformation_finite_prefixes μ Q f hfin),hs,
      ENNReal.ofReal_mul (bellmanRatio_nonneg μ N Q),ENNReal.mul_div_cancel_right
        (ENNReal.ofReal_ne_zero_iff.mpr hw) ENNReal.ofReal_ne_top]
  have he : informationRatio μ N Q = ENNReal.ofReal (bellmanRatio μ N Q) :=
    le_antisymm (informationRatio_le_bellmanRatio μ N Q hfin)
      (hr.symm.le.trans (le_iSup_of_le f (le_iSup_of_le hf (le_iSup_of_le hi le_rfl))))
  exact ⟨he,hf,hi,hr.trans he.symm⟩

theorem informationRatio_bellman_zero (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : FourPriors) (hN : 0 < N)
    (hfin : ∀ n k, n ≤ N → k ≤ n → prefixInformation μ Q n k ≠ ⊤) (κ : ℝ) :
    rootBellman (prefixReward μ Q) (prefixCoefficient μ Q.work) κ (N-1) = 0 ↔
      κ = (informationRatio μ N Q).toReal := by
  rw [(informationRatio_bellman_attained μ N Q hN hfin).1,
    ENNReal.toReal_ofReal (bellmanRatio_nonneg μ N Q)]
  exact rootBellman_zero_iff _ _ (prefixCoefficient_nonneg μ Q.work) _ _

end ThresholdHC.StoppingProgram
