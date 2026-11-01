import ThresholdHC.EntropyTailLower.Specification
import ThresholdHC.EntropyTailLower.WeightedOverlap

/-! Weighted finite-gap sign entropy, derived from observable stopping
windows. The weights may vanish and need not sum to one. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.CriticalEntropy

theorem signTest_exponential_sum {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : SignTest R)
    {K : ℕ} (d : Fin K → EntropyGap)
    (hgap : ∀ i j, j.val = i.val+1 → 2*(d j : ℝ) ≤ (d i : ℝ))
    (hfinite : ∀ i, expectedSignTestWork ν (signParameter (d i) false) A ≠ ∞)
    (herror : ∀ i b, (ν.prod (Tier2.tapeMeasure (signParameter (d i) b))).real
      {z | A.output z ≠ b} ≤ 1/10) :
    (∑ i, exp (-65*((d i : ℝ)^2*
      (expectedSignTestWork ν (signParameter (d i) false) A).toReal))) ≤ 32768*exp 8 := by
  classical
  let cost := fun i : Fin K => (d i : ℝ)^2*
    (expectedSignTestWork ν (signParameter (d i) false) A).toReal
  let events := fun i : Fin K => signTestWindow A (entropyLowerTime (d i))
    (entropyUpperTime (expectedSignTestWork ν (signParameter (d i) false) A).toReal)
  let P := ν.prod (Tier2.tapeMeasure ⟨1/2,by norm_num⟩)
  have hm (i : Fin K) : MeasurableSet (events i) := measurable_signTestWindow A _ _
  have hi (i : Fin K) : Integrable ((events i).indicator (fun _ => exp (-cost i))) P :=
    (integrable_const _).indicator (hm i)
  have hbound := integral_mono (integrable_finsetSum Finset.univ (fun i _ => hi i))
    (integrable_const (32768:ℝ)) (signTest_exponential_overlap ν A d hgap)
  rw [integral_finsetSum _ (fun i _ => hi i)] at hbound
  have heq (i : Fin K) :
      (∫ z, (events i).indicator (fun _ => exp (-cost i)) z ∂P) =
        exp (-cost i)*P.real (events i) := by
    rw [integral_indicator_const _ (hm i)]
    simp [smul_eq_mul,mul_comm]
  simp only [heq,integral_const,probReal_univ,one_smul] at hbound
  have hmass (i : Fin K) : exp (-64*cost i-8) ≤ P.real (events i) :=
    signTest_fair_window ν A (d i) (by simpa using herror i false)
      (by simpa using herror i true) (hfinite i)
  have hterm (i : Fin K) : exp (-65*cost i-8) ≤ exp (-cost i)*P.real (events i) := by
    have h := mul_le_mul_of_nonneg_left (hmass i) (exp_pos (-cost i)).le
    rw [← exp_add] at h
    convert h using 1; congr 1; ring
  have hsum : (∑ i, exp (-65*cost i-8)) ≤ 32768 :=
    (Finset.sum_le_sum (fun i _ => hterm i)).trans hbound
  have hscale := mul_le_mul_of_nonneg_left hsum (exp_pos (8:ℝ)).le
  rw [Finset.mul_sum] at hscale
  have hs (i : Fin K) : exp 8*exp (-65*cost i-8) = exp (-65*cost i) := by
    rw [← exp_add]
    congr 1
    ring
  simp only [hs] at hscale
  simpa only [mul_comm] using hscale

/-- Universal weighted sign-testing bound with a conservative coefficient.
It requires finite negative-sign work only and no fair-law stopping premise. -/
theorem weighted_sign_entropy : WeightedSignEntropyStatement := by
  intro R _ ν _ A K d hgap hfinite herror a ha
  let cost := fun i : Fin K => (d i : ℝ)^2*
    (expectedSignTestWork ν (signParameter (d i) false) A).toReal
  let p := fun i : Fin K => exp (-65*cost i)/(32768*exp 8)
  have hp (i : Fin K) : 0 < p i := by dsimp [p]; positivity
  have hsum : (∑ i, p i) ≤ 1 := by
    simp only [p,← Finset.sum_div]
    apply (div_le_one (by positivity : (0:ℝ) < 32768*exp 8)).mpr
    exact signTest_exponential_sum ν A d hgap hfinite herror
  have hc (i : Fin K) : (1/128:ℝ) ≤ cost i :=
    ThresholdHC.CriticalAllSizes.single_gap_work ν A (d i) (hfinite i)
      (by simpa using herror i false) (by simpa using herror i true)
  have hlog : log (32768:ℝ) ≤ 15 := by
    have he : log (32768:ℝ) = 15*log 2 := by
      convert log_pow (2:ℝ) 15 using 1; norm_num
    rw [he]
    have h := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h
    linarith
  have hpoint (i : Fin K) : 1-log (p i) ≤ 4096*cost i := by
    dsimp [p]
    rw [log_div (exp_pos _).ne' (by positivity),log_exp,
      log_mul (by norm_num : (32768:ℝ) ≠ 0) (exp_pos _).ne',log_exp]
    linarith [hc i]
  calc
    _ ≤ ∑ i, a i*(1-log (p i)) :=
      ThresholdHC.EntropyTailQuantile.costEntropy_le_reference ha hp hsum
    _ ≤ ∑ i, a i*(4096*cost i) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (ha i))
    _ = 4096*∑ i, a i*cost i := by rw [Finset.mul_sum]; congr 1; funext i; ring

end ThresholdHC.EntropyTailLower
