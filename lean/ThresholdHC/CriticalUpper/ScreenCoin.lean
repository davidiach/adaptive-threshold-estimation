import ThresholdHC.CriticalUpper.ScreenWork
import ThresholdHC.CriticalEntropy.CriticalLaw

/-! Error and actual stopped work under the Bernoulli tape law. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal

theorem screen_cost_integrable (A₀ A₁ : ℝ) (L : ℕ) (p : unitInterval) :
    Integrable (fun ω => (screenCost A₀ A₁ L ω : ℝ)) (Tier2.tapeMeasure p) := by
  simpa only [screenCost,cap,dyadicMean,Nat.cast_pow,Nat.cast_ofNat] using
    integrable_screenWork (μ := Tier2.tapeMeasure p) A₀ A₁
      (fun _k => measurable_prefixMean Tier2.measurable_observations _) L

theorem screen_expected_work_real (A₀ A₁ : ℝ) (L : ℕ) (p : unitInterval) :
    expectedStoppedProcedureWork (Measure.dirac ()) p (screenProcedure A₀ A₁ L) =
      ENNReal.ofReal (∫ ω, (screenCost A₀ A₁ L ω : ℝ) ∂Tier2.tapeMeasure p) := by
  have hf : Measurable (fun z : Unit × (ℕ → Bool) => ENNReal.ofReal (screenCost A₀ A₁ L z.2 : ℝ)) :=
    ENNReal.measurable_ofReal.comp ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      ((measurable_screenCost A₀ A₁ L).comp measurable_snd))
  calc
    _ = ∫⁻ z : Unit × (ℕ → Bool), ENNReal.ofReal (screenCost A₀ A₁ L z.2 : ℝ)
        ∂(Measure.dirac ()).prod (Tier2.tapeMeasure p) := by
      unfold expectedStoppedProcedureWork
      apply lintegral_congr
      intro z
      simp [stoppedProcedureWork,screenProcedure,BlindUpper.finiteStoppedProcedure]
    _ = ∫⁻ ω, ENNReal.ofReal (screenCost A₀ A₁ L ω : ℝ) ∂Tier2.tapeMeasure p := by
      rw [lintegral_prod _ hf.aemeasurable]
      simp
    _ = _ := (ofReal_integral_eq_lintegral_ofReal (screen_cost_integrable A₀ A₁ L p)
      (ae_of_all _ (fun ω => Nat.cast_nonneg (screenCost A₀ A₁ L ω)))).symm

theorem screen_coin_error (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (L : ℕ) (d : ℝ) (hd : d ∈ Ioc (0 : ℝ) (1/4)) (b : Bool) :
    (Tier2.tapeMeasure (criticalParameter d b)).real {ω | screenValue A₀ A₁ L ω ≠ Tier2.bit b} ≤
      Real.exp (-2*cap L*d^2)+(L : ℝ)*Real.exp (-(if b then A₀ else A₁)) := by
  have ht := Tier2.tape_mean_tails (criticalParameter d b)
  rw [criticalParameter_coe_of_mem d hd b] at ht
  cases b with
  | false =>
    simp only [Bool.false_eq_true,ite_false,← sub_eq_add_neg] at ht
    simpa only [screenValue,Tier2.bit,Bool.false_eq_true,ite_false] using
      screen_error_negative A₀ A₁ hA₁ L hd.1 ht
  | true =>
    simp only [ite_true] at ht
    simpa only [screenValue,Tier2.bit,ite_true] using screen_error_positive A₀ A₁ hA₀ L hd.1 ht

theorem screen_coin_work (A₀ A₁ : ℝ) (hA₀ : 1 ≤ A₀) (hA₁ : 1 ≤ A₁)
    (L : ℕ) (d : ℝ) (hd : d ∈ Ioc (0 : ℝ) (1/4)) (b : Bool) :
    expectedStoppedProcedureWork (Measure.dirac ()) (criticalParameter d b) (screenProcedure A₀ A₁ L) ≤
      ENNReal.ofReal (min (cap L) (10*(if b then A₁ else A₀)/d^2)) := by
  rw [screen_expected_work_real]
  apply ENNReal.ofReal_le_ofReal
  have ht := Tier2.tape_mean_tails (criticalParameter d b)
  rw [criticalParameter_coe_of_mem d hd b] at ht
  have hdmax : d ≤ 1/2 := by linarith [hd.2]
  cases b with
  | false =>
    simp only [Bool.false_eq_true,ite_false,← sub_eq_add_neg] at ht
    simpa only [screenCost,cap,Nat.cast_pow,Nat.cast_ofNat,Bool.false_eq_true,ite_false] using
      screen_work_negative A₀ A₁ hA₀ L hd.1 hdmax ht
  | true =>
    simp only [ite_true] at ht
    simpa only [screenCost,cap,Nat.cast_pow,Nat.cast_ofNat,ite_true] using
      screen_work_positive A₀ A₁ hA₁ L hd.1 hdmax ht

end ThresholdHC.CriticalUpper
