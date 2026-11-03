import ThresholdHC.EntropyTailLower.CertificateCentering
import ThresholdHC.StoppingProgram.ConstantInformation

noncomputable section
open MeasureTheory Real
open scoped BigOperators
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram
open ThresholdHC.CapIdentification

theorem constantPrior_countMean {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) (u : CountState N → ℝ) :
    countMean μ (constantPrior r hr) u =
      r*countMean μ (constantPrior 1 (by norm_num)) u+
        (1-r)*countMean μ (constantPrior 0 (by norm_num)) u := by
  unfold countMean
  simp_rw [constantPrior_countCoefficient μ r hr,add_mul,mul_assoc]
  simp only [Finset.sum_add_distrib,Finset.mul_sum]

theorem certificate_small_bias_label_floor {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (C : Certificate N) (hC : Feasible μ ρ B C) (hb : C.bias ≤ ρ/128) :
    ρ ≤ 16*B*C.variance := by
  have hi : 0 < intensity C.flow := by
    rcases certificate_large_bias_or_positive_intensity μ ρ B hρ.le hρ1 C hC with h | h
    · linarith
    · exact h
  let D := centeredCertificate μ C
  have hD : Feasible μ ρ B D := centeredCertificate_feasible μ ρ B hρ.le C hC hi
  let q := constantPrior ρ ⟨hρ.le,hρ1⟩
  let qone := constantPrior 1 (by norm_num)
  have hz : constantPrior 0 (by norm_num) = nullSignLaw := rfl
  have hq : RarePrior μ ρ q := le_of_eq (constantPrior_mean μ _ _)
  have hnull : RarePrior μ ρ nullSignLaw := by simpa [RarePrior,signMean,nullSignLaw] using hρ.le
  have hm0 : countMean μ nullSignLaw D.flow.outputWeight = 0 :=
    centeredCertificate_null_mean μ C hC.cone hi
  have hbq := hD.bias_bound q hq
  have hqmean : signMean μ q.val = ρ := constantPrior_mean μ _ _
  rw [hqmean] at hbq
  change |0+countMean μ q D.flow.outputWeight-ρ| ≤ 2*C.bias at hbq
  simp only [zero_add] at hbq
  change |countMean μ (constantPrior ρ ⟨hρ.le,hρ1⟩) D.flow.outputWeight-ρ| ≤ 2*C.bias at hbq
  rw [constantPrior_countMean,hz,hm0,mul_zero,add_zero] at hbq
  have hmean : (1/2:ℝ) ≤ countMean μ qone D.flow.outputWeight := by
    apply (mul_le_mul_iff_right₀ hρ).mp
    have hh := (abs_le.mp hbq).1
    change _ ≤ ρ*countMean μ qone D.flow.outputWeight-ρ at hh
    linarith
  have hm := hD.variance_bound q hq
  change countMean μ (constantPrior ρ ⟨hρ.le,hρ1⟩) D.flow.momentWeight ≤ 4*C.variance at hm
  rw [constantPrior_countMean,hz] at hm
  have hm0nonneg := countMean_nonneg μ nullSignLaw D.flow.momentWeight hD.cone.moment_nonneg
  have hm1 : ρ*countMean μ qone D.flow.momentWeight ≤ 4*C.variance := by
    nlinarith only [hm,mul_nonneg (sub_nonneg.mpr hρ1) hm0nonneg]
  have hw : intensity C.flow ≤ B :=
    (flow_work_ge_intensity μ nullSignLaw C.flow hC.cone).trans (hC.work_bound nullSignLaw hnull)
  have hs := flow_countMean_square μ qone D.flow hD.cone
  change (countMean μ qone D.flow.outputWeight)^2 ≤ intensity C.flow*countMean μ qone D.flow.momentWeight at hs
  have hsmean : (1/4:ℝ) ≤ (countMean μ qone D.flow.outputWeight)^2 := by nlinarith only [hmean]
  have hresult : ρ/4 ≤ B*(4*C.variance) := by
    calc
      _ ≤ ρ*(countMean μ qone D.flow.outputWeight)^2 := by
        nlinarith only [mul_le_mul_of_nonneg_left hsmean hρ.le]
      _ ≤ intensity C.flow*(ρ*countMean μ qone D.flow.momentWeight) := by
        nlinarith only [mul_le_mul_of_nonneg_left hs hρ.le]
      _ ≤ intensity C.flow*(4*C.variance) := mul_le_mul_of_nonneg_left hm1 hi.le
      _ ≤ B*(4*C.variance) := mul_le_mul_of_nonneg_right hw (by positivity [hC.variance_nonneg])
  linarith

theorem certificate_label_floor {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hB : 0 < B) (C : Certificate N) (hC : Feasible μ ρ B C) :
    min ρ (sqrt (ρ/B)) ≤ 128*C.bias+4*sqrt C.variance := by
  by_cases hb : C.bias ≤ ρ/128
  · have hf := certificate_small_bias_label_floor μ ρ B hρ hρ1 C hC hb
    have hdiv : ρ/B ≤ 16*C.variance := (div_le_iff₀ hB).mpr (by nlinarith only [hf])
    have hs := sqrt_le_sqrt hdiv
    rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 16)] at hs
    norm_num at hs
    have hm := min_le_right ρ (sqrt (ρ/B))
    nlinarith only [hs,hm,hC.bias_nonneg]
  · have hm := min_le_left ρ (sqrt (ρ/B))
    have hs := sqrt_nonneg C.variance
    linarith

theorem certificate_bounded_entropy_cost {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hB : 0 < B) (C : Certificate N) (hC : Feasible μ ρ B C)
    (F : ℝ) (_hF : 0 ≤ F) (hFmax : F ≤ 16384) :
    min ρ (sqrt (ρ*F/B)) ≤ 16384*C.bias+512*sqrt C.variance := by
  have hs : sqrt (ρ*F/B) ≤ 128*sqrt (ρ/B) := by
    have hh : ρ*F/B ≤ 16384*(ρ/B) := by
      have hm := mul_le_mul_of_nonneg_left hFmax (div_nonneg hρ.le hB.le)
      convert hm using 1 <;> ring
    have hh' := sqrt_le_sqrt hh
    rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 16384)] at hh'
    norm_num at hh'
    exact hh'
  have hm : min ρ (sqrt (ρ*F/B)) ≤ 128*min ρ (sqrt (ρ/B)) := by
    rcases le_total ρ (sqrt (ρ/B)) with h | h
    · rw [min_eq_left h]
      have hh := min_le_left ρ (sqrt (ρ*F/B))
      linarith
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans hs
  have hf := certificate_label_floor μ ρ B hρ hρ1 hB C hC
  linarith

end ThresholdHC.EntropyTailLower
