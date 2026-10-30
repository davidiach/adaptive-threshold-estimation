import ThresholdHC.Genie.SingularPrefixBound
import ThresholdHC.Genie.FlowDepth

/-! The information/work bound holds for every finite count flow, not only
fixed-depth policies. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

theorem singular_flow_information {N : ℕ} (f : Flow N) (hf : FlowCone f) :
    flowInformation uniformGapLaw singularExamplePriors f ≤
      ENNReal.ofReal (3/4*countMean uniformGapLaw singularExamplePriors.work f.continueWeight) := by
  have hfin (n k : ℕ) (_ : n ≤ N) (hk : k ≤ n) :
      prefixInformation uniformGapLaw singularExamplePriors n k ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (singular_prefix_information n k hk)
  have hF := flowInformation_finite_prefixes uniformGapLaw singularExamplePriors f hfin
  rw [←ENNReal.ofReal_toReal hF]
  apply ENNReal.ofReal_le_ofReal
  rw [flowInformation_toReal_raw uniformGapLaw singularExamplePriors f hf hfin]
  have hI : (∑ n ∈ Finset.range (N+1), rawLayer f.stopWeight (prefixReward uniformGapLaw singularExamplePriors) n) ≤
      3/8*countMean uniformGapLaw uniformSignPrior f.continueWeight := by
    rw [←stopping_depth_countMean uniformGapLaw uniformSignPrior f hf,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    unfold rawLayer
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k ≤ n := by have h := Finset.mem_range.mp hk; omega
    have hp := ENNReal.toReal_mono ENNReal.ofReal_ne_top (singular_prefix_information n k hk')
    rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity : (0:ℝ) ≤ 3/8*(n:ℝ))
      (prefixCoefficient_nonneg uniformGapLaw uniformSignPrior n k))] at hp
    have hm := mul_le_mul_of_nonneg_left hp (rawArray_nonneg _ hf.stop_nonneg n k)
    change rawArray f.stopWeight n k*(prefixInformation uniformGapLaw singularExamplePriors n k).toReal ≤ _
    nlinarith [hm]
  have hW : countMean uniformGapLaw uniformSignPrior f.continueWeight ≤
      2*countMean uniformGapLaw singularExamplePriors.work f.continueWeight := by
    rw [←rawLayer_countMean,←rawLayer_countMean,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    unfold rawLayer
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have h := singular_work_prefix n k
    rw [←uniform_prefix_moment] at h
    have hm := mul_le_mul_of_nonneg_left h (rawArray_nonneg _ hf.continue_nonneg n k)
    nlinarith [hm]
  linarith

theorem singular_informationRatio_bound (N : ℕ) :
    informationRatio uniformGapLaw N singularExamplePriors ≤ ENNReal.ofReal (3/4) := by
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  apply iSup_le
  intro _hi
  apply ENNReal.div_le_of_le_mul
  rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3/4)]
  exact singular_flow_information f hf

theorem singular_infiniteInformationRatio_bound :
    infiniteInformationRatio uniformGapLaw singularExamplePriors ≤ ENNReal.ofReal (3/4) :=
  iSup_le (fun n => singular_informationRatio_bound (n+1))

end ThresholdHC.Genie
