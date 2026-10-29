import ThresholdHC.RareAboveTwo.BandError
import ThresholdHC.RareAboveTwo.Terminal
import ThresholdHC.CriticalUpper.CoinLaw
import ThresholdHC.ObservableSimulation.OriginalExperiment

/-! Calibrated binary decisions and their error under the actual population
mixture, uniformly over every measurable globally rare sign law. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Tier6 ThresholdHC.Uniform713 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation

def calibratedCost (a ρ : ℝ) (j : ℕ) : (ℕ → Bool) → ℕ :=
  bandCost (initialLevel a) (negativeThreshold j) (positiveThreshold ρ j) (terminalLevel ρ j)

def calibratedValue (a ρ : ℝ) (j : ℕ) : (ℕ → Bool) → ℝ :=
  bandValue (initialLevel a) (negativeThreshold j) (positiveThreshold ρ j) (terminalLevel ρ j)

theorem measurable_calibratedCost (a ρ : ℝ) (j : ℕ) : Measurable (calibratedCost a ρ j) :=
  measurable_bandCost _ _ _ _

theorem measurable_calibratedValue (a ρ : ℝ) (j : ℕ) : Measurable (calibratedValue a ρ j) :=
  measurable_bandValue _ _ _ _

theorem calibratedValue_binary (a ρ : ℝ) (j : ℕ) (ω : ℕ → Bool) :
    calibratedValue a ρ j ω = 0 ∨ calibratedValue a ρ j ω = 1 :=
  by unfold calibratedValue bandValue; exact bandDecision_zero_or_one _ _ _ _ _

theorem calibrated_prefix_ext (a ρ : ℝ) (j : ℕ) (ω ω' : ℕ → Bool)
    (h : Tier2.tapePrefix (calibratedCost a ρ j ω) ω = Tier2.tapePrefix (calibratedCost a ρ j ω) ω') :
    calibratedCost a ρ j ω' = calibratedCost a ρ j ω ∧ calibratedValue a ρ j ω' = calibratedValue a ρ j ω :=
  band_prefix_ext _ _ _ _ _ _ h

theorem originalTape_integral_mixture (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (F : (ℕ → Bool) → ℝ) (hF : Measurable F) (M : ℝ) (hbound : ∀ ω, |F ω| ≤ M) :
    (∫ ω, F ω ∂originalPopulationTapeLaw μ q) =
      ∫ d, q.val d*(∫ ω, F ω ∂Tier2.tapeMeasure (gapParameter true d))+
        (1-q.val d)*(∫ ω, F ω ∂Tier2.tapeMeasure (gapParameter false d)) ∂μ := by
  let : IsProbabilityMeasure (populationMeasure μ (Measure.dirac ())) := by
    unfold populationMeasure
    infer_instance
  let P := populationInput (R := Unit) (gapParameter false) (gapParameter true) (signUnit q)
  have hp := populationInput_preserving μ (Measure.dirac ()) (gapParameter false) (gapParameter true)
    (signUnit q) (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)
  have hT : MeasurePreserving (fun z => (P z).2) (populationMeasure μ (Measure.dirac ()))
      (originalPopulationTapeLaw μ q) :=
    (measurePreserving_snd (μ := Measure.dirac ()) (ν := originalPopulationTapeLaw μ q)).comp hp
  rw [← hT.map_eq,integral_map hT.measurable.aemeasurable hF.aestronglyMeasurable]
  have hi : Integrable (fun z => F (P z).2) (populationMeasure μ (Measure.dirac ())) := by
    apply Integrable.of_bound (hF.comp hT.measurable).aestronglyMeasurable M
    exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Function.comp_apply] using hbound _)
  unfold populationMeasure at *
  rw [population_integral μ (Measure.dirac ()) _ _ (signUnit q)
    (fun z => F z.2) (hF.comp measurable_snd) hi]
  simp_rw [CriticalUpper.integral_dirac_unit_tape F hF M hbound]
  rfl

def calibratedError (a ρ : ℝ) (j : ℕ) (b : Bool) (d : Gap) : ℝ :=
  ∫ ω, |calibratedValue a ρ j ω-Tier2.bit b| ∂Tier2.tapeMeasure (gapParameter b d)

theorem calibratedError_bounds (a ρ : ℝ) (j : ℕ) (b : Bool) (d : Gap) :
    0 ≤ calibratedError a ρ j b d ∧ calibratedError a ρ j b d ≤ 1 := by
  refine ⟨integral_nonneg (fun _ => abs_nonneg _),?_⟩
  have hp (ω) : |calibratedValue a ρ j ω-Tier2.bit b| ≤ 1 := by
    rcases calibratedValue_binary a ρ j ω with h | h <;> cases b <;> simp [h,Tier2.bit]
  have hi : Integrable (fun ω => |calibratedValue a ρ j ω-Tier2.bit b|) (Tier2.tapeMeasure (gapParameter b d)) :=
    ((integrable_binary (measurable_calibratedValue a ρ j) (calibratedValue_binary a ρ j)).sub (integrable_const _)).abs
  simpa [calibratedError] using integral_mono hi (integrable_const (1 : ℝ)) hp

theorem measurable_calibratedError (a ρ : ℝ) (j : ℕ) (b : Bool) :
    Measurable (calibratedError a ρ j b) :=
  (CriticalUpper.measurable_tape_integral (fun ω => |calibratedValue a ρ j ω-Tier2.bit b|)
    (((measurable_calibratedValue a ρ j).sub measurable_const).abs)).comp (measurable_gapParameter b)

theorem calibratedError_probability (a ρ : ℝ) (j : ℕ) (b : Bool) (d : Gap) :
    calibratedError a ρ j b d = (Tier2.tapeMeasure (gapParameter b d)).real
      {ω | calibratedValue a ρ j ω ≠ Tier2.bit b} :=
  integral_binary_error (measurable_calibratedValue a ρ j) measurable_const
    (calibratedValue_binary a ρ j) (fun _ => by cases b <;> simp [Tier2.bit])

theorem calibratedError_bound (a ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (j : ℕ) (b : Bool) (d : Gap) :
    calibratedError a ρ j b d ≤
      Real.exp (-2*cap (initialLevel a+terminalLevel ρ j)*(d : ℝ)^2)+
        (if b then CriticalUpper.screenAccuracy j else ρ*CriticalUpper.screenAccuracy j) := by
  rw [calibratedError_probability]
  have ht := Tier2.tape_mean_tails (gapParameter b d)
  cases b with
  | false =>
    change HasMeanTails _ _ (1/2-(d : ℝ)) at ht
    have h := band_error_negative (initialLevel a) (negativeThreshold j) (positiveThreshold ρ j)
      (positiveThreshold_nonneg ρ hρ hρ1 j) (terminalLevel ρ j) d.property.1 ht
    simpa only [calibratedValue,bandValue,Tier2.bit,Bool.false_eq_true,ite_false] using h.trans (add_le_add le_rfl (positiveThreshold_error ρ hρ j _))
  | true =>
    change HasMeanTails _ _ (1/2+(d : ℝ)) at ht
    have h := band_error_positive (initialLevel a) (negativeThreshold j) (positiveThreshold ρ j)
      (negativeThreshold_nonneg j) (terminalLevel ρ j) d.property.1 ht
    simpa only [calibratedValue,bandValue,Tier2.bit,ite_true] using h.trans (add_le_add le_rfl (negativeThreshold_error j _))

def populationError (μ : Measure Gap) (q : SignLaw) (a ρ : ℝ) (j : ℕ) : ℝ :=
  ∫ d, q.val d*calibratedError a ρ j true d+(1-q.val d)*calibratedError a ρ j false d ∂μ

theorem populationError_integrable (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (a ρ : ℝ) (j : ℕ) :
    Integrable (fun d => q.val d*calibratedError a ρ j true d+
      (1-q.val d)*calibratedError a ρ j false d) μ := by
  apply Integrable.of_bound
    ((q.property.1.mul (measurable_calibratedError a ρ j true)).add
      ((measurable_const.sub q.property.1).mul (measurable_calibratedError a ρ j false))).aestronglyMeasurable 1
  refine ae_of_all _ (fun d => ?_)
  have hp := calibratedError_bounds a ρ j true d
  have hn := calibratedError_bounds a ρ j false d
  have hq := q.property.2 d
  have h₀ : 0 ≤ q.val d*calibratedError a ρ j true d+(1-q.val d)*calibratedError a ρ j false d :=
    add_nonneg (mul_nonneg hq.1 hp.1) (mul_nonneg (sub_nonneg.mpr hq.2) hn.1)
  dsimp only [Pi.add_apply,Pi.mul_apply,Pi.sub_apply]
  rw [Real.norm_of_nonneg h₀]
  nlinarith [mul_le_mul_of_nonneg_left hp.2 hq.1,mul_le_mul_of_nonneg_left hn.2 (sub_nonneg.mpr hq.2)]

theorem populationError_bound (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a ρ : ℝ) (hα : 2 < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : PowerMargin μ α a) (q : SignLaw)
    (hq : RarePrior μ ρ q) (j : ℕ) : populationError μ q a ρ j ≤ 3*ρ*CriticalUpper.screenAccuracy j := by
  let g : Gap → ℝ := fun d => Real.exp (-2*cap (initialLevel a+terminalLevel ρ j)*(d : ℝ)^2)
  have hg : Integrable g μ := by
    apply Integrable.of_bound (show Measurable g by unfold g; fun_prop).aestronglyMeasurable 1
    exact ae_of_all _ (fun d => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (d : ℝ),cap_pos (initialLevel a+terminalLevel ρ j)]))
  have hqi : Integrable q.val μ := by
    apply Integrable.of_bound q.property.1.aestronglyMeasurable 1
    exact ae_of_all _ (fun d => by rw [Real.norm_of_nonneg (q.property.2 d).1]; exact (q.property.2 d).2)
  have hi := (hg.add (hqi.mul_const (CriticalUpper.screenAccuracy j))).add (integrable_const (ρ*CriticalUpper.screenAccuracy j))
  have hpt (d : Gap) : q.val d*calibratedError a ρ j true d+(1-q.val d)*calibratedError a ρ j false d ≤
      g d+q.val d*CriticalUpper.screenAccuracy j+ρ*CriticalUpper.screenAccuracy j := by
    have hp := mul_le_mul_of_nonneg_left (calibratedError_bound a ρ hρ hρ1 j true d) (q.property.2 d).1
    have hn := mul_le_mul_of_nonneg_left (calibratedError_bound a ρ hρ hρ1 j false d) (sub_nonneg.mpr (q.property.2 d).2)
    simp only [ite_true,Bool.false_eq_true,ite_false] at hp hn
    dsimp [g]
    nlinarith [mul_nonneg (q.property.2 d).1 (mul_pos hρ (CriticalUpper.screenAccuracy_pos j)).le]
  have h := integral_mono (populationError_integrable μ q a ρ j) hi hpt
  simp only [Pi.add_apply] at h
  have he := integral_add (hg.add (hqi.mul_const (CriticalUpper.screenAccuracy j)))
    (integrable_const (μ := μ) (ρ*CriticalUpper.screenAccuracy j))
  simp only [Pi.add_apply] at he
  rw [he,integral_add hg (hqi.mul_const _),integral_mul_const,integral_const] at h
  simp only [probReal_univ,smul_eq_mul,one_mul] at h
  have hgauss := terminal_gaussian_error μ α a ρ hα ha ha' hρ hρ1 hm j
  have hmass := mul_le_mul_of_nonneg_right hq (CriticalUpper.screenAccuracy_pos j).le
  change (∫ d, q.val d ∂μ)*CriticalUpper.screenAccuracy j ≤ _ at hmass
  change populationError μ q a ρ j ≤ _ at h
  change (∫ d, g d ∂μ) ≤ _ at hgauss
  nlinarith only [h,hgauss,hmass]

end ThresholdHC.RareAboveTwo
