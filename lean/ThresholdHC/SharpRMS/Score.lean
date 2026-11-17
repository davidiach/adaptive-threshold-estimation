import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Uniform-prior score inequality for the intermediate budgets. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory Set Filter
open scoped Topology

private def taper (t : ℝ) := 1-t^2

private theorem taper_deriv (t : ℝ) : HasDerivAt taper (-2*t) t := by
  convert ((hasDerivAt_id t).pow 2).const_sub 1 using 1
  · rfl
  · simp

/-- Integrated risk-work inequality obtained from the score. A zero-mass
word is permitted when its derivative also vanishes. -/
theorem finite_score_tradeoff {I : Type} [Fintype I] (P D : I → ℝ → ℝ) (X : I → ℝ)
    (hp : ∀ i t, t ∈ Ioo (-1:ℝ) 1 → 0 ≤ P i t ∧ (P i t = 0 → D i t = 0))
    (hD : ∀ i, Continuous (D i)) (hd : ∀ i t, HasDerivAt (P i) (D i t) t)
    (mass : ∀ t ∈ Icc (-1:ℝ) 1, ∑ i, P i t = 1)
    (K : ℝ → ℝ) (hK : IntervalIntegrable K volume (-1) 1)
    (price : ∀ t ∈ Ioo (-1:ℝ) 1, (1-t^2)^2 * (∑ i, (D i t)^2/P i t) ≤ K t)
    : (40/3:ℝ) ≤ 36*(∫ t in (-1:ℝ)..1, ∑ i, P i t*(X i-t)^2) + ∫ t in (-1:ℝ)..1, K t := by
  classical
  let W := fun i t => taper t*P i t
  let W' := fun i t => taper t*D i t-2*t*P i t
  let F := fun t => ∑ i, (X i-t)*W' i t
  let A := fun t => ∑ i, P i t*(X i-t)^2
  have pc i : Continuous (P i) := continuous_iff_continuousAt.mpr (fun t => (hd i t).continuousAt)
  have wc i : Continuous (W i) := by dsimp [W,taper]; fun_prop
  have w'c i : Continuous (W' i) := by dsimp [W',taper]; fun_prop
  have fc : Continuous F := by dsimp [F]; fun_prop
  have ac : Continuous A := by dsimp [A]; fun_prop
  have derivW (i) (t : ℝ) : HasDerivAt (W i) (W' i t) t := by
    convert (taper_deriv t).mul (hd i t) using 1
    dsimp [W']; ring
  have identity (i : I) :
      (∫ t in (-1:ℝ)..1, (X i-t)*W' i t) = ∫ t in (-1:ℝ)..1, W i t := by
    have hderiv (t : ℝ) : HasDerivAt (fun y => (X i-y)*W i y) ((X i-t)*W' i t-W i t) t := by
      convert ((hasDerivAt_id t).const_sub (X i)).mul (derivW i t) using 1
      · rfl
      · dsimp; ring
    have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (-1:ℝ)) (b := 1)
      (fun t _ => hderiv t) (Continuous.intervalIntegrable (by fun_prop) ..)
    have hi : IntervalIntegrable (fun t => (X i-t)*W' i t) volume (-1) 1 :=
      Continuous.intervalIntegrable (by fun_prop) ..
    rw [intervalIntegral.integral_sub hi ((wc i).intervalIntegrable ..)] at hft
    norm_num [W,taper] at hft
    exact sub_eq_zero.mp hft
  have meanF : (∫ t in (-1:ℝ)..1, F t) = 4/3 := by
    unfold F
    rw [intervalIntegral.integral_finsetSum (fun i _ => Continuous.intervalIntegrable (by fun_prop) ..)]
    simp_rw [identity]
    rw [← intervalIntegral.integral_finsetSum (fun i _ => (wc i).intervalIntegrable ..)]
    have eqI : (∫ t in (-1:ℝ)..1, ∑ i, W i t) = ∫ t in (-1:ℝ)..1, 1-t^2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht
      simp only [W, ← Finset.mul_sum,mass t ht,mul_one,taper]
    rw [eqI,intervalIntegral.integral_sub (intervalIntegrable_const) (Continuous.intervalIntegrable (by fun_prop) ..),
      intervalIntegral.integral_const,integral_pow]
    norm_num
  have dnorm (t : ℝ) (ht : t ∈ Ioo (-1:ℝ) 1) : ∑ i, D i t = 0 := by
    have dm := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i t)
    have hlocal : (fun y => ∑ i, P i y) =ᶠ[𝓝 t] (fun _=>1) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy
      exact mass y ⟨hy.1.le,hy.2.le⟩
    exact (dm.congr_of_eventuallyEq hlocal.symm).unique (hasDerivAt_const t 1)
  have point (t : ℝ) (ht : t ∈ Ioo (-1:ℝ) 1) :
      12*F t ≤ 36*A t + K t + 4*t^2 := by
    have atom (i : I) : 12*((X i-t)*W' i t) ≤ 36*(P i t*(X i-t)^2) +
        (taper t)^2*((D i t)^2/P i t) - 4*t*taper t*(D i t) + 4*t^2*(P i t) := by
      dsimp [W']
      by_cases hz : P i t = 0
      · simp [hz,(hp i t ht).2 hz]
      have h := sq_nonneg (6*P i t*(X i-t)-(taper t*D i t-2*t*P i t))
      have pos := lt_of_le_of_ne (hp i t ht).1 (Ne.symm hz)
      field_simp
      linarith only [h]
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => atom i)
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
      dnorm t ht,mul_zero,sub_zero,mass t ⟨ht.1.le,ht.2.le⟩,mul_one] at hh
    exact hh.trans (by dsimp [F,A,taper] at *; linarith only [price t ht])
  have fi : IntervalIntegrable (fun t => 12*F t) volume (-1) 1 :=
    Continuous.intervalIntegrable (by fun_prop) ..
  have ai : IntervalIntegrable (fun t => 36*A t) volume (-1) 1 :=
    Continuous.intervalIntegrable (by fun_prop) ..
  have ti : IntervalIntegrable (fun t : ℝ => 4*t^2) volume (-1) 1 :=
    Continuous.intervalIntegrable (by fun_prop) ..
  have upper := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (-1:ℝ) ≤ 1)
    fi ((ai.add hK).add ti) point
  have split := intervalIntegral.integral_add (ai.add hK) ti
  change (∫ t in (-1:ℝ)..1, 12*F t) ≤ ∫ t in (-1:ℝ)..1, 36*A t+K t+4*t^2 at upper
  rw [split,intervalIntegral.integral_add ai hK,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,meanF,integral_pow] at upper
  norm_num at upper
  change _ ≤ 36*(∫ t in (-1:ℝ)..1, A t) + ∫ t in (-1:ℝ)..1, K t
  linarith

/-- Enough integrated Fisher control forces worst-case sign-mean MSE at
least 1/9, as witnessed by the uniform prior. -/
theorem finite_score_risk {I : Type} [Fintype I] (P D : I → ℝ → ℝ) (X : I → ℝ)
    (hp : ∀ i t, t ∈ Ioo (-1:ℝ) 1 → 0 ≤ P i t ∧ (P i t = 0 → D i t = 0))
    (hD : ∀ i, Continuous (D i)) (hd : ∀ i t, HasDerivAt (P i) (D i t) t)
    (mass : ∀ t ∈ Icc (-1:ℝ) 1, ∑ i, P i t = 1)
    (K : ℝ → ℝ) (hK : IntervalIntegrable K volume (-1) 1)
    (price : ∀ t ∈ Ioo (-1:ℝ) 1, (1-t^2)^2 * (∑ i, (D i t)^2/P i t) ≤ K t)
    (budget : (∫ t in (-1:ℝ)..1, K t) ≤ 16/3) :
    (2/9:ℝ) ≤ ∫ t in (-1:ℝ)..1, ∑ i, P i t*(X i-t)^2 := by
  linarith only [finite_score_tradeoff P D X hp hD hd mass K hK price,budget]

end ThresholdHC.SharpRMS
