import ThresholdHC.ShiftedPower.Classifier

noncomputable section
open MeasureTheory Set Real
namespace ThresholdHC.ShiftedPower
open ThresholdHC.Tier6 ThresholdHC.Tier2 ThresholdHC.ObservableSimulation ThresholdHC.RareAboveTwo
open ThresholdHC.CriticalUpper

private theorem mixture_integrable (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (F : (ℕ → Bool) → ℝ) (hF : Measurable F) (hbin : ∀ ω, F ω = 0 ∨ F ω = 1) :
    Integrable (fun d : Gap => q.val d*(∫ ω, F ω ∂tapeMeasure (gapParameter true d))+
      (1-q.val d)*(∫ ω, F ω ∂tapeMeasure (gapParameter false d))) μ := by
  have hm (b) : Measurable (fun d : Gap => ∫ ω, F ω ∂tapeMeasure (gapParameter b d)) :=
    (measurable_tape_integral F hF).comp (measurable_gapParameter b)
  have hbound (b) (d : Gap) : (∫ ω, F ω ∂tapeMeasure (gapParameter b d)) ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact integral_nonneg (fun ω => (by rcases hbin ω with h|h <;> simp [h]))
    · calc (∫ ω, F ω ∂tapeMeasure (gapParameter b d)) ≤ ∫ _ : ℕ → Bool, (1:ℝ) ∂tapeMeasure (gapParameter b d) := by
             apply integral_mono_of_nonneg (ae_of_all _ (fun ω => (by rcases hbin ω with h|h <;> simp [h]))) (integrable_const _)
             exact ae_of_all _ (fun ω => (hbin ω).elim (fun h => by rw [h]; norm_num) (fun h => by rw [h]))
           _ = 1 := by simp
  apply (integrable_const (1:ℝ)).mono'
    (((q.property.1.mul (hm true)).add ((measurable_const.sub q.property.1).mul (hm false))).aestronglyMeasurable)
  apply ae_of_all
  intro d
  have ht := hbound true d
  have hf := hbound false d
  have hq := q.property.2 d
  dsimp only [Pi.add_apply,Pi.mul_apply,Pi.sub_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (add_nonneg (mul_nonneg hq.1 ht.1) (mul_nonneg (by linarith) hf.1))]
  nlinarith only [mul_le_mul_of_nonneg_left ht.2 hq.1,mul_le_mul_of_nonneg_left hf.2 (sub_nonneg.mpr hq.2)]

theorem population_nonnegative_bound (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (F : (ℕ → Bool) → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ ω, |F ω| ≤ M)
    (hpos : ∀ ω, 0 ≤ F ω) (g : Gap → ℝ) (hg : Integrable g μ)
    (h : ∀ (d : Gap) (S : Bool), (∫ ω, F ω ∂tapeMeasure (gapParameter S d)) ≤ g d) :
    (∫ ω, F ω ∂originalPopulationTapeLaw μ q) ≤ ∫ d, g d ∂μ := by
  rw [originalTape_integral_mixture μ q F hF M hM]
  refine integral_mono_of_nonneg ?_ hg ?_
  · exact ae_of_all _ (fun d => add_nonneg (mul_nonneg (q.property.2 d).1 (integral_nonneg hpos))
      (mul_nonneg (sub_nonneg.mpr (q.property.2 d).2) (integral_nonneg hpos)))
  · apply ae_of_all
    intro d
    have hq := q.property.2 d
    have ht := mul_le_mul_of_nonneg_left (h d true) hq.1
    have hf := mul_le_mul_of_nonneg_left (h d false) (sub_nonneg.mpr hq.2)
    linarith only [ht,hf]

theorem population_bias (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (F : (ℕ → Bool) → ℝ) (hF : Measurable F) (hbin : ∀ ω, F ω = 0 ∨ F ω = 1)
    (g : Gap → ℝ) (hg : Integrable g μ)
    (h : ∀ (d : Gap) (S : Bool), |(∫ ω, F ω ∂tapeMeasure (gapParameter S d))-bit S| ≤ g d) :
    |(∫ ω, F ω ∂originalPopulationTapeLaw μ q)-signMean μ q.val| ≤ ∫ d, g d ∂μ := by
  rw [originalTape_integral_mixture μ q F hF 1 (fun ω => (hbin ω).elim (fun h => by simp [h]) (fun h => by simp [h]))]
  have hqint : Integrable q.val μ := (integrable_const (1:ℝ)).mono' q.property.1.aestronglyMeasurable
    (ae_of_all _ (fun d => by rw [Real.norm_of_nonneg (q.property.2 d).1]; exact (q.property.2 d).2))
  rw [signMean,← integral_sub (mixture_integrable μ q F hF hbin) hqint]
  apply (abs_integral_le_integral_abs).trans
  apply integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _)) hg
  apply ae_of_all
  intro d
  let m (S) := ∫ ω, F ω ∂tapeMeasure (gapParameter S d)
  have ht : |m true-1| ≤ g d := by simpa [m,bit] using h d true
  have hf : |m false| ≤ g d := by simpa [m,bit] using h d false
  have hq := q.property.2 d
  change |q.val d*m true+(1-q.val d)*m false-q.val d| ≤ _
  rw [show q.val d*m true+(1-q.val d)*m false-q.val d = q.val d*(m true-1)+(1-q.val d)*m false by ring]
  calc _ ≤ |q.val d*(m true-1)|+|(1-q.val d)*m false| := abs_add_le _ _
       _ = q.val d*|m true-1|+(1-q.val d)*|m false| := by rw [abs_mul,abs_mul,abs_of_nonneg hq.1,abs_of_nonneg (sub_nonneg.mpr hq.2)]
       _ ≤ q.val d*g d+(1-q.val d)*g d := add_le_add
         (mul_le_mul_of_nonneg_left ht hq.1) (mul_le_mul_of_nonneg_left hf (sub_nonneg.mpr hq.2))
       _ = _ := by ring

end ThresholdHC.ShiftedPower
