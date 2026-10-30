import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Elementary beta-moment recurrence, with no special-function formula. -/

noncomputable section
open MeasureTheory
namespace ThresholdHC.Genie

def uniformMonomial (a b : ℕ) (p : ℝ) : ℝ := p^a*(1-p)^b
def uniformMoment (a b : ℕ) : ℝ := ∫ p in (0:ℝ)..1, uniformMonomial a b p

theorem uniformMonomial_continuous (a b : ℕ) : Continuous (uniformMonomial a b) := by
  unfold uniformMonomial
  fun_prop

theorem uniformMoment_nonneg (a b : ℕ) : 0 ≤ uniformMoment a b := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro p hp
  exact mul_nonneg (pow_nonneg hp.1 _) (pow_nonneg (sub_nonneg.mpr hp.2) _)

theorem uniformMoment_pos (a b : ℕ) : 0 < uniformMoment a b := by
  apply intervalIntegral.integral_pos (by norm_num) (uniformMonomial_continuous a b).continuousOn
  · intro p hp
    exact mul_nonneg (pow_nonneg hp.1.le _) (pow_nonneg (sub_nonneg.mpr hp.2) _)
  · refine ⟨1/2,by norm_num,?_⟩
    unfold uniformMonomial
    positivity

theorem uniformMoment_harmonic (a b : ℕ) :
    uniformMoment a (b+1)+uniformMoment (a+1) b = uniformMoment a b := by
  unfold uniformMoment
  rw [←intervalIntegral.integral_add ((uniformMonomial_continuous _ _).intervalIntegrable _ _)
    ((uniformMonomial_continuous _ _).intervalIntegrable _ _)]
  congr 1
  funext p
  simp only [uniformMonomial,pow_succ]
  ring

theorem uniformMoment_balance (a b : ℕ) :
    ((a:ℝ)+1)*uniformMoment a (b+1) = ((b:ℝ)+1)*uniformMoment (a+1) b := by
  have hd (p : ℝ) : HasDerivAt (uniformMonomial (a+1) (b+1))
      (((a:ℝ)+1)*uniformMonomial a (b+1) p-((b:ℝ)+1)*uniformMonomial (a+1) b p) p := by
    have h := ((hasDerivAt_id p).pow (a+1)).mul (((hasDerivAt_id p).const_sub 1).pow (b+1))
    convert h using 1
    · funext x
      rfl
    · simp only [uniformMonomial,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,
        id_eq,Pi.pow_apply,mul_one,Pi.mul_apply]
      ring
  have hi : IntervalIntegrable (fun p => ((a:ℝ)+1)*uniformMonomial a (b+1) p-
      ((b:ℝ)+1)*uniformMonomial (a+1) b p) volume 0 1 :=
    (((uniformMonomial_continuous _ _).const_mul _).sub
      ((uniformMonomial_continuous _ _).const_mul _)).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun p _ => hd p) hi
  rw [intervalIntegral.integral_sub
    (((uniformMonomial_continuous _ _).const_mul _).intervalIntegrable _ _)
    (((uniformMonomial_continuous _ _).const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at h
  change _*uniformMoment a (b+1)-_*uniformMoment (a+1) b = _ at h
  simp only [uniformMonomial,sub_self,zero_pow (Nat.succ_ne_zero _),mul_zero,zero_mul,sub_zero] at h
  linarith

theorem uniformMoment_recurrence (a b : ℕ) :
    ((a:ℝ)+b+2)*uniformMoment a (b+1) = ((b:ℝ)+1)*uniformMoment a b := by
  have h := uniformMoment_balance a b
  have he := uniformMoment_harmonic a b
  nlinarith

end ThresholdHC.Genie
