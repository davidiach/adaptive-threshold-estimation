import ThresholdHC.Genie.RevealFiniteness
import ThresholdHC.StoppingProgram.InformationBellman

/-! The same charged Bellman recursion characterizes the genie program,
with latent-reveal rewards substituted at its terminal layer. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

def genieReward (μ : Measure Gap) (Q : FourPriors) (N n k : ℕ) : ℝ :=
  (geniePrefixInformation μ Q N n k).toReal

theorem genieFlowInformation_toReal_raw {N : ℕ} (μ : Measure Gap) [IsFiniteMeasure μ]
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) (f : Flow N) (hf : FlowCone f) :
    (genieFlowInformation μ Q f).toReal =
      ∑ n ∈ Finset.range (N+1), rawLayer f.stopWeight (genieReward μ Q N) n := by
  unfold genieFlowInformation eRawLayer
  have hfin (n k : ℕ) := geniePrefixInformation_finite μ Q hC N n k
  rw [ENNReal.toReal_sum (fun n hn => ENNReal.sum_ne_top.mpr (fun k hk =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin n k)))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [ENNReal.toReal_sum (fun k hk => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin n k))]
  unfold rawLayer
  apply Finset.sum_congr rfl
  intro k hk
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (rawArray_nonneg _ hf.stop_nonneg n k)]
  rfl

def genieBellmanRatio (μ : Measure Gap) (N : ℕ) (Q : FourPriors) : ℝ :=
  ratioValue (rootInformation (genieReward μ Q N) (N-1))
    (rootWork (prefixCoefficient μ Q.work) (N-1))

theorem genieBellmanRatio_nonneg (μ : Measure Gap) (N : ℕ) (Q : FourPriors) :
    0 ≤ genieBellmanRatio μ N Q := by
  apply ratioValue_nonneg
  · intro a
    exact add_nonneg (treeInformation_nonneg _ (fun _ _ => ENNReal.toReal_nonneg) _ _ _ _)
      (treeInformation_nonneg _ (fun _ _ => ENNReal.toReal_nonneg) _ _ _ _)
  · intro a
    unfold rootWork
    positivity [treeWork_nonneg _ (prefixCoefficient_nonneg μ Q.work) (N-1) 1 0 a.1,
      treeWork_nonneg _ (prefixCoefficient_nonneg μ Q.work) (N-1) 1 1 a.2]

theorem genieFlowScore_information {N : ℕ} (μ : Measure Gap) [IsFiniteMeasure μ] (Q : FourPriors)
    (f : Flow N) (hf : FlowCone f) (κ : ℝ)
    (hC : latentDivergence μ Q ≠ ⊤) :
    rawFlowScore f (genieReward μ Q N) (prefixCoefficient μ Q.work) κ =
      (genieFlowInformation μ Q f).toReal-κ*countMean μ Q.work f.continueWeight := by
  rw [genieFlowInformation_toReal_raw μ Q hC f hf,← rawLayer_countMean]
  unfold rawFlowScore rawLayer
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem genieInformationRatio_le_genieBellmanRatio (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : FourPriors)
    (hC : latentDivergence μ Q ≠ ⊤) :
    genieInformationRatio μ N Q ≤ ENNReal.ofReal (genieBellmanRatio μ N Q) := by
  have hzero : rootBellman (genieReward μ Q N) (prefixCoefficient μ Q.work)
      (genieBellmanRatio μ N Q) (N-1) = 0 :=
    (rootBellman_zero_iff _ _ (prefixCoefficient_nonneg μ Q.work) _ _).mpr rfl
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  apply iSup_le
  intro hi
  have hs := flowScore_le_rootBellman f hf (genieReward μ Q N) (prefixCoefficient μ Q.work)
    (genieBellmanRatio μ N Q) (prefixCoefficient_root μ Q.work)
  rw [genieFlowScore_information μ Q f hf _ hC,hzero,mul_zero,sub_nonpos] at hs
  have hw : 0 < countMean μ Q.work f.continueWeight := by
    have h := flow_work_ge_intensity μ Q.work f hf
    rw [hi] at h
    linarith
  apply (ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr hw) ENNReal.ofReal_ne_top).mpr
  rw [← ENNReal.ofReal_toReal (genieFlowInformation_finite μ Q hC f hf),
    ← ENNReal.ofReal_mul (genieBellmanRatio_nonneg μ N Q)]
  exact ENNReal.ofReal_le_ofReal hs

theorem genieInformationRatio_bellman_attained (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : FourPriors) (hN : 0 < N)
    (hC : latentDivergence μ Q ≠ ⊤) :
    genieInformationRatio μ N Q = ENNReal.ofReal (genieBellmanRatio μ N Q) ∧
    let f := bellmanFlow (genieReward μ Q N) (prefixCoefficient μ Q.work) (genieBellmanRatio μ N Q) N
    FlowCone f ∧ intensity f = 1 ∧
      genieFlowInformation μ Q f/ENNReal.ofReal (countMean μ Q.work f.continueWeight) = genieInformationRatio μ N Q := by
  let f := bellmanFlow (genieReward μ Q N) (prefixCoefficient μ Q.work) (genieBellmanRatio μ N Q) N
  have hf : FlowCone f := bellmanFlow_cone _ _ _ hN
  have hi : intensity f = 1 := bellmanFlow_intensity _ _ _ _
  have hzero : rootBellman (genieReward μ Q N) (prefixCoefficient μ Q.work)
      (genieBellmanRatio μ N Q) (N-1) = 0 :=
    (rootBellman_zero_iff _ _ (prefixCoefficient_nonneg μ Q.work) _ _).mpr rfl
  have hs := bellmanFlow_score (genieReward μ Q N) (prefixCoefficient μ Q.work) (genieBellmanRatio μ N Q)
    hN (prefixCoefficient_root μ Q.work)
  change rawFlowScore f _ _ _ = _ at hs
  rw [genieFlowScore_information μ Q f hf _ hC,hzero,sub_eq_zero] at hs
  have hw : 0 < countMean μ Q.work f.continueWeight := by
    have h := flow_work_ge_intensity μ Q.work f hf
    rw [hi] at h
    linarith
  have hr : genieFlowInformation μ Q f/ENNReal.ofReal (countMean μ Q.work f.continueWeight) =
      ENNReal.ofReal (genieBellmanRatio μ N Q) := by
    rw [← ENNReal.ofReal_toReal (genieFlowInformation_finite μ Q hC f hf),hs,
      ENNReal.ofReal_mul (genieBellmanRatio_nonneg μ N Q),ENNReal.mul_div_cancel_right
        (ENNReal.ofReal_ne_zero_iff.mpr hw) ENNReal.ofReal_ne_top]
  have he : genieInformationRatio μ N Q = ENNReal.ofReal (genieBellmanRatio μ N Q) :=
    le_antisymm (genieInformationRatio_le_genieBellmanRatio μ N Q hC)
      (hr.symm.le.trans (le_iSup_of_le f (le_iSup_of_le hf (le_iSup_of_le hi le_rfl))))
  exact ⟨he,hf,hi,hr.trans he.symm⟩

theorem genieInformationRatio_bellman_zero (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : FourPriors) (hN : 0 < N)
    (hC : latentDivergence μ Q ≠ ⊤) (κ : ℝ) :
    rootBellman (genieReward μ Q N) (prefixCoefficient μ Q.work) κ (N-1) = 0 ↔
      κ = (genieInformationRatio μ N Q).toReal := by
  rw [(genieInformationRatio_bellman_attained μ N Q hN hC).1,
    ENNReal.toReal_ofReal (genieBellmanRatio_nonneg μ N Q)]
  exact rootBellman_zero_iff _ _ (prefixCoefficient_nonneg μ Q.work) _ _

theorem genieInformationRatio_bellman_certificate (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : FourPriors) (hN : 0 < N) (hC : latentDivergence μ Q ≠ ⊤)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    genieInformationRatio μ N Q ≤ ENNReal.ofReal κ ↔
      rootBellman (genieReward μ Q N) (prefixCoefficient μ Q.work) κ (N-1) ≤ 0 := by
  rw [(genieInformationRatio_bellman_attained μ N Q hN hC).1,
    ENNReal.ofReal_le_ofReal_iff hκ,rootBellman_eq_priceValue]
  symm
  apply priceValue_le_zero_iff
  intro a
  unfold rootWork
  positivity [treeWork_nonneg _ (prefixCoefficient_nonneg μ Q.work) (N-1) 1 0 a.1,
    treeWork_nonneg _ (prefixCoefficient_nonneg μ Q.work) (N-1) 1 1 a.2]

end ThresholdHC.Genie
