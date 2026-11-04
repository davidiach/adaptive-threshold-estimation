import ThresholdHC.ShiftedPower.Mixture

noncomputable section
open MeasureTheory Real Set
namespace ThresholdHC.ShiftedPower
open ThresholdHC.Tier6 ThresholdHC.Tier2 ThresholdHC.EntropyTailExecution ThresholdHC.RareAboveTwo
open ThresholdHC.ObservableSimulation

def resolution (k : ℕ) : ℝ := (Real.sqrt ((2:ℝ)^k))⁻¹
def errorBound (α a : ℝ) (k : ℕ) : ℝ := (resolution k/a)^α/(1-α/4)
def workPower (α : ℝ) : ℝ := (α+2)/2
def workBound (α a : ℝ) (k : ℕ) : ℝ :=
  17*(1/(1-workPower α/2))*(2:ℝ)^k*((resolution k/a)^α/(1-α/workPower α))

theorem resolution_pos (k : ℕ) : 0 < resolution k := by unfold resolution; positivity

theorem kernel_integrable (ν : Measure Gap) [IsFiniteMeasure ν] {h p : ℝ} (hh : 0 ≤ h) :
    Integrable (fun d : Gap => min 1 ((h/(d:ℝ))^p)) ν := by
  apply (integrable_const (1:ℝ)).mono'
    ((measurable_const.min ((measurable_const.div measurable_subtype_coe).pow_const p)).aestronglyMeasurable)
  exact ae_of_all _ (fun d => by
    dsimp only [Pi.div_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (le_min zero_le_one (Real.rpow_nonneg (div_nonneg hh d.property.1.le) _))]
    exact min_le_left _ _)

private theorem error_eq (k : ℕ) (d : Gap) :
    errorKernel k d = min 1 ((resolution k/(d:ℝ))^(4:ℝ)) := by
  have hs : (resolution k/(d:ℝ))^2 = ((2:ℝ)^k*(d:ℝ)^2)⁻¹ := by
    dsimp [resolution]
    rw [div_pow,inv_pow,Real.sq_sqrt (by positivity : 0 ≤ (2:ℝ)^k)]
    field_simp
  unfold errorKernel
  rw [show ((resolution k/(d:ℝ))^(4:ℝ)) = ((resolution k/(d:ℝ))^2)^2 by norm_num only [Real.rpow_ofNat]; ring,hs]

theorem error_integral (ν : Measure Gap) [IsProbabilityMeasure ν] {α a : ℝ}
    (hα : 0 < α) (hu : α < 2) (ha : 0 < a) (hm : PowerMargin ν α a) (k : ℕ) :
    (∫ d, errorKernel k d ∂ν) ≤ errorBound α a k := by
  simp_rw [error_eq]
  exact power_kernel_bound ν hm ha (resolution_pos k) hα (by norm_num) (by linarith)

private theorem error_integrable (ν : Measure Gap) [IsFiniteMeasure ν] (k : ℕ) :
    Integrable (errorKernel k) ν := by
  have he : errorKernel k = fun d : Gap => min 1 ((resolution k/(d:ℝ))^(4:ℝ)) := funext (error_eq k)
  rw [he]
  exact kernel_integrable ν (resolution_pos k).le

theorem population_classifier_bias (ν : Measure Gap) [IsProbabilityMeasure ν] (q : SignLaw) {α a : ℝ}
    (hα : 0 < α) (hu : α < 2) (ha : 0 < a) (hm : PowerMargin ν α a) (k : ℕ) :
    |(∫ ω, (classifierCall k).value ω ∂originalPopulationTapeLaw ν q)-signMean ν q.val| ≤ errorBound α a k :=
  (population_bias ν q _ (classifierCall k).measurable_value (classifierCall_binary k) _
    (error_integrable ν k) (classifierCall_bias k)).trans (error_integral ν hα hu ha hm k)

theorem population_classifier_difference (ν : Measure Gap) [IsProbabilityMeasure ν] (q : SignLaw)
    {α a : ℝ} (hα : 0 < α) (hu : α < 2) (ha : 0 < a) (hm : PowerMargin ν α a) (k l : ℕ) :
    (∫ ω, ((classifierCall k).value ω-(classifierCall l).value ω)^2 ∂originalPopulationTapeLaw ν q) ≤
      errorBound α a k+errorBound α a l := by
  have hmF := ((classifierCall k).measurable_value.sub (classifierCall l).measurable_value).pow_const 2
  have hM (ω) : |((classifierCall k).value ω-(classifierCall l).value ω)^2| ≤ 1 := by
    rcases classifierCall_binary k ω with hk|hk <;> rcases classifierCall_binary l ω with hl|hl <;> simp [hk,hl]
  have hb := population_nonnegative_bound ν q _ hmF 1 hM (fun ω => sq_nonneg _)
    (fun d => errorKernel k d+errorKernel l d) ((error_integrable ν k).add (error_integrable ν l))
    (classifierCall_difference k l)
  rw [integral_add (error_integrable ν k) (error_integrable ν l)] at hb
  exact hb.trans (add_le_add (error_integral ν hα hu ha hm k) (error_integral ν hα hu ha hm l))

theorem population_classifier_work (ν : Measure Gap) [IsProbabilityMeasure ν] (q : SignLaw)
    {α a : ℝ} (hα : 0 < α) (hu : α < 2) (ha : 0 < a) (hm : PowerMargin ν α a) (k : ℕ) :
    (∫ ω, ((classifierCall k).cost ω:ℝ) ∂originalPopulationTapeLaw ν q) ≤ workBound α a k := by
  let p := workPower α
  have hp : 1 ≤ p := by dsimp [p,workPower]; linarith
  have hp' : α < p := by dsimp [p,workPower]; linarith
  have hp2 : p/2 < 1 := by dsimp [p,workPower]; linarith
  have hp0 : 0 ≤ p/2 := by positivity
  let C := 17*(1/(1-p/2))*(2:ℝ)^k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let g (d : Gap) := C*min 1 ((resolution k/(d:ℝ))^p)
  have hg : Integrable g ν := (kernel_integrable ν (resolution_pos k).le).const_mul C
  have hb := population_nonnegative_bound ν q _ ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (classifierCall k).measurable_cost) ((2:ℝ)^k)
    (fun ω => by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact classifierCall_cap k ω) (fun _ => Nat.cast_nonneg _) g hg
    (fun d S => (classifierCall_work k d S).trans (by
      have h := mul_le_mul_of_nonneg_left (log_work_bound (n := (2:ℝ)^k) (by positivity) d.property.1 hp0 hp2) (by norm_num : 0 ≤ (17:ℝ))
      simpa only [g,C,resolution,ThresholdHC.Uniform713.workEnvelope,ThresholdHC.Uniform713.cap,
        show 2*(p/2)=p by ring,mul_assoc] using h))
  rw [integral_const_mul] at hb
  have he := power_kernel_bound ν hm ha (resolution_pos k) hα hp hp'
  exact hb.trans (mul_le_mul_of_nonneg_left he hC)

end ThresholdHC.ShiftedPower
