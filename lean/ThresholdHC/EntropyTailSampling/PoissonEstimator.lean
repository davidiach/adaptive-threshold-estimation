import ThresholdHC.EntropyTailSampling.CountedMarks
import ThresholdHC.BlindUpper.ProductionAverage

/-! Unbiased Poisson-normalized averages and exact mean-square error.
The normalizer is the deterministic mean, never the realized count. -/

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace ThresholdHC.EntropyTailSampling
open ThresholdHC.EntropyTailUpper
variable {X : Type} [MeasurableSpace X]

def poissonAverage (r : ℝ≥0) (Y : X → ℝ) (z : ℕ × (ℕ → X)) : ℝ :=
  (r:ℝ)⁻¹*countedSum Y z

theorem measurable_poissonAverage (r : ℝ≥0) (Y : X → ℝ) (hY : Measurable Y) :
    Measurable (poissonAverage r Y) := measurable_const.mul (measurable_countedSum Y hY)

theorem poissonAverage_memLp (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    (Y : X → ℝ) (hYm : Measurable Y) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ x, ‖Y x‖ ≤ K) :
    MemLp (poissonAverage r Y) 2 (markedPoissonLaw ν r) :=
  (countedSum_memLp ν r Y hYm hK0 hK).const_mul _

theorem poissonAverage_mean (ν : Measure X) [IsProbabilityMeasure ν] {r : ℝ≥0}
    (hr : 0 < (r:ℝ)) (Y : X → ℝ) (hYm : Measurable Y) {K : ℝ} (hK : ∀ x, ‖Y x‖ ≤ K) :
    (∫ z, poissonAverage r Y z ∂markedPoissonLaw ν r) = ∫ x, Y x ∂ν := by
  have hY : MemLp Y 2 ν := MemLp.of_bound hYm.aestronglyMeasurable K (ae_of_all _ hK)
  unfold poissonAverage
  rw [integral_const_mul, countedSum_mean ν r Y hYm hY hK]
  exact inv_mul_cancel_left₀ hr.ne' _

theorem countedSum_variance (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    (Y : X → ℝ) (hYm : Measurable Y) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ x, ‖Y x‖ ≤ K) :
    variance (countedSum Y) (markedPoissonLaw ν r) = (r:ℝ)*(∫ x, (Y x)^2 ∂ν) := by
  have hY : MemLp Y 2 ν := MemLp.of_bound hYm.aestronglyMeasurable K (ae_of_all _ hK)
  have h := variance_eq_sub (countedSum_memLp ν r Y hYm hK0 hK)
  dsimp only [Pi.pow_apply] at h
  rw [countedSum_mean ν r Y hYm hY hK, countedSum_second ν r Y hYm hY hK0 hK] at h
  nlinarith only [h]

theorem poissonAverage_variance (ν : Measure X) [IsProbabilityMeasure ν] {r : ℝ≥0}
    (hr : 0 < (r:ℝ)) (Y : X → ℝ) (hYm : Measurable Y)
    {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ x, ‖Y x‖ ≤ K) :
    variance (poissonAverage r Y) (markedPoissonLaw ν r) = (∫ x, (Y x)^2 ∂ν)/(r:ℝ) := by
  unfold poissonAverage
  rw [variance_const_mul, countedSum_variance ν r Y hYm hK0 hK]
  field_simp

theorem poissonAverage_mse (ν : Measure X) [IsProbabilityMeasure ν] {r : ℝ≥0}
    (hr : 0 < (r:ℝ)) (Y : X → ℝ) (hYm : Measurable Y)
    {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ x, ‖Y x‖ ≤ K) (a : ℝ) :
    (∫ z, (poissonAverage r Y z-a)^2 ∂markedPoissonLaw ν r) =
      (∫ x, (Y x)^2 ∂ν)/(r:ℝ)+((∫ x, Y x ∂ν)-a)^2 := by
  rw [ThresholdHC.BlindUpper.mse_eq_variance_add_bias _ _ (poissonAverage_memLp ν r Y hYm hK0 hK),
    poissonAverage_variance ν hr Y hYm hK0 hK, poissonAverage_mean ν hr Y hYm hK]

theorem poissonAverage_squaredRisk (ν : Measure X) [IsProbabilityMeasure ν] {r : ℝ≥0}
    (hr : 0 < (r:ℝ)) (Y : X → ℝ) (hYm : Measurable Y)
    {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ x, ‖Y x‖ ≤ K) (a : ℝ) :
    (∫⁻ z, ENNReal.ofReal ((poissonAverage r Y z-a)^2) ∂markedPoissonLaw ν r) =
      ENNReal.ofReal ((∫ x, (Y x)^2 ∂ν)/(r:ℝ)+((∫ x, Y x ∂ν)-a)^2) := by
  have hi : Integrable (fun z => (poissonAverage r Y z-a)^2) (markedPoissonLaw ν r) :=
    ((poissonAverage_memLp ν r Y hYm hK0 hK).sub (memLp_const a)).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => sq_nonneg _)),
    poissonAverage_mse ν hr Y hYm hK0 hK]

theorem countedCost_mean (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    (C : X → ℝ) (hCm : Measurable C) {K : ℝ} (hC0 : ∀ x, 0 ≤ C x) (hK : ∀ x, C x ≤ K) :
    (∫⁻ z, ENNReal.ofReal (countedSum C z) ∂markedPoissonLaw ν r) =
      ENNReal.ofReal ((r:ℝ)*(∫ x, C x ∂ν)) := by
  have hb : ∀ x, ‖C x‖ ≤ K := fun x => by rw [Real.norm_of_nonneg (hC0 x)]; exact hK x
  have hC : MemLp C 2 ν := MemLp.of_bound hCm.aestronglyMeasurable K (ae_of_all _ hb)
  have hn : ∀ z : ℕ × (ℕ → X), 0 ≤ countedSum C z := by
    intro z
    unfold countedSum prefixSum
    exact Finset.sum_nonneg (fun (i : Fin z.1) _ => hC0 (z.2 i.val))
  rw [← ofReal_integral_eq_lintegral_ofReal (countedSum_integrable ν r C hCm hb) (ae_of_all _ hn),
    countedSum_mean ν r C hCm hC hb]

end ThresholdHC.EntropyTailSampling
