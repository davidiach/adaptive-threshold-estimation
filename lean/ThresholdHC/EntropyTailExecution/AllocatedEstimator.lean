import ThresholdHC.EntropyTailExecution.RealizedPoisson
import ThresholdHC.EntropyTailExecution.IncrementBounds
import ThresholdHC.RareAboveTwo.Nonvacuity
import ThresholdHC.RareAboveTwo.BudgetMath

/-! Optimal positive Poisson allocation is realized by an observable estimator.
The bounds concern the unchanged original expected-budget and RMS-risk model. -/

noncomputable section
open MeasureTheory Real
open scoped NNReal ENNReal BigOperators

namespace ThresholdHC.EntropyTailExecution
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.EntropyTailUpper
open ThresholdHC.RareAboveTwo

def allocationRates {J : ℕ} (B : ℝ) (v c : Fin (J+1) → ℝ) : Fin (J+1) → ℝ≥0 :=
  fun i => Real.toNNReal (allocationMean B v c i)

theorem allocationRates_coe {J : ℕ} {B : ℝ} {v c : Fin (J+1) → ℝ}
    (hB : 0 < B) (hv : ∀ i, 0 < v i) (hc : ∀ i, 0 < c i) (i : Fin (J+1)) :
    (allocationRates B v c i:ℝ) = allocationMean B v c i :=
  Real.coe_toNNReal _ (allocationMean_pos hB hv hc i).le

theorem allocationRates_pos {J : ℕ} {B : ℝ} {v c : Fin (J+1) → ℝ}
    (hB : 0 < B) (hv : ∀ i, 0 < v i) (hc : ∀ i, 0 < c i) (i : Fin (J+1)) :
    0 < (allocationRates B v c i:ℝ) := by
  rw [allocationRates_coe hB hv hc]
  exact allocationMean_pos hB hv hc i

def allocatedEstimator {J : ℕ} (B : ℝ) (v c : Fin (J+1) → ℝ)
    (D : Fin (J+1) → FiniteCall) : AdaptiveEstimator (Fin (J+1) → ℕ) :=
  poissonPlanEstimator (allocationRates B v c)
    (fun i => scaleCall ((allocationRates B v c i:ℝ)⁻¹) (D i))

theorem allocated_work_bound {J : ℕ} {B : ℝ} {v c : Fin (J+1) → ℝ}
    (hB : 0 < B) (hv : ∀ i, 0 < v i) (hc : ∀ i, 0 < c i)
    (D : Fin (J+1) → FiniteCall) {K : Fin (J+1) → ℝ}
    (hK : ∀ i ω, ((D i).cost ω:ℝ) ≤ K i)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (hC : ∀ i, (∫ ω, ((D i).cost ω:ℝ) ∂originalPopulationTapeLaw μ q) ≤ c i) :
    expectedWork μ (allocatedEstimator B v c D) q ≤ ENNReal.ofReal B := by
  unfold allocatedEstimator
  rw [poissonPlan_expectedWork _ (fun i => scaleCall ((allocationRates B v c i:ℝ)⁻¹) (D i)) μ q
    (fun i ω => hK i ω)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∑ i, (allocationRates B v c i:ℝ)*c i :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hC i) (allocationRates_pos hB hv hc i).le)
    _ = B := by
      simp only [allocationRates_coe hB hv hc, mul_comm]
      exact allocationMean_work hv hc

theorem allocated_mse_bound {J : ℕ} {B : ℝ} {v c : Fin (J+1) → ℝ}
    (hB : 0 < B) (hv : ∀ i, 0 < v i) (hc : ∀ i, 0 < c i)
    (D : Fin (J+1) → FiniteCall) {U : Fin (J+1) → ℝ}
    (hU0 : ∀ i, 0 ≤ U i) (hU : ∀ i ω, ‖(D i).value ω‖ ≤ U i)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (a : ℝ)
    (hV : ∀ i, (∫ ω, ((D i).value ω)^2 ∂originalPopulationTapeLaw μ q) ≤ v i)
    {b : ℝ} (hb : 0 ≤ b)
    (hbias : |(∑ i, ∫ ω, (D i).value ω ∂originalPopulationTapeLaw μ q)-a| ≤ b) :
    squaredRisk (experimentLaw μ (allocatedEstimator B v c D) q)
      (populationOutput (allocatedEstimator B v c D)) a ≤
      ENNReal.ofReal ((allocationCertificate v c)^2/B+b^2) := by
  unfold allocatedEstimator
  rw [poissonPlan_squaredRisk _ (allocationRates_pos hB hv hc) _ (fun i => (D i).value)
    (fun i => (D i).measurable_value) (fun _ _ => rfl) hU0 hU]
  apply ENNReal.ofReal_le_ofReal
  have hs : (∑ i, (∫ ω, ((D i).value ω)^2 ∂originalPopulationTapeLaw μ q)/
      (allocationRates B v c i:ℝ)) ≤ (allocationCertificate v c)^2/B := by
    calc
      _ ≤ ∑ i, v i/(allocationRates B v c i:ℝ) :=
        Finset.sum_le_sum (fun i _ => div_le_div_of_nonneg_right (hV i) (allocationRates_pos hB hv hc i).le)
      _ = _ := by simp only [allocationRates_coe hB hv hc]; exact allocationMean_variance hB hv hc
  apply add_le_add hs
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).mpr hbias

theorem allocated_rootRisk_bound {J : ℕ} {B : ℝ} {v c : Fin (J+1) → ℝ}
    (hB : 0 < B) (hv : ∀ i, 0 < v i) (hc : ∀ i, 0 < c i)
    (D : Fin (J+1) → FiniteCall) {U : Fin (J+1) → ℝ}
    (hU0 : ∀ i, 0 ≤ U i) (hU : ∀ i ω, ‖(D i).value ω‖ ≤ U i)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (a : ℝ)
    (hV : ∀ i, (∫ ω, ((D i).value ω)^2 ∂originalPopulationTapeLaw μ q) ≤ v i)
    {b : ℝ} (hb : 0 ≤ b)
    (hbias : |(∑ i, ∫ ω, (D i).value ω ∂originalPopulationTapeLaw μ q)-a| ≤ b) :
    rootMeanRisk (experimentLaw μ (allocatedEstimator B v c D) q)
      (populationOutput (allocatedEstimator B v c D)) a ≤
      ENNReal.ofReal (b+allocationCertificate v c/sqrt B) := by
  have hs := allocated_mse_bound hB hv hc D hU0 hU μ q a hV hb hbias
  have hA := (allocationCertificate_pos hv hc).le
  have hS := (sqrt_pos.mpr hB).le
  have he : (allocationCertificate v c)^2/B = (allocationCertificate v c/sqrt B)^2 := by
    rw [div_pow, sq_sqrt hB.le]
  have hbound : (allocationCertificate v c)^2/B+b^2 ≤ (b+allocationCertificate v c/sqrt B)^2 := by
    rw [he]
    nlinarith [mul_nonneg hb (div_nonneg hA hS)]
  have hr := ENNReal.rpow_le_rpow (hs.trans (ENNReal.ofReal_le_ofReal hbound))
    (by norm_num : (0:ℝ) ≤ 1/2)
  rw [ofReal_square_rpow_half _ (add_nonneg hb (div_nonneg hA hS))] at hr
  exact hr

end ThresholdHC.EntropyTailExecution
