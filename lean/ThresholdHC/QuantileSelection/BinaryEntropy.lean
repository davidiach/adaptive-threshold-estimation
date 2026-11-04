import ThresholdHC.EntropyTailQuantile.CostEntropy
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open Real Set
namespace ThresholdHC.QuantileSelection

/-- The sign of the derivative of binary entropy divided by its geometric mean. -/
theorem entropy_slope_nonneg {p : ℝ} (hp : p ∈ Icc 0 (1/2 : ℝ)) :
    0 ≤ negMulLog p - negMulLog (1-p) := by
  let g := fun x : ℝ => negMulLog x - negMulLog (1-x)
  have hd {x : ℝ} (hx : x ∈ Ioo 0 (1/2 : ℝ)) :
      HasDerivAt g (-log (x*(1-x))-2) x := by
    have h := (hasDerivAt_negMulLog hx.1.ne').sub
      ((hasDerivAt_negMulLog (x := 1-x) (by linarith [hx.2])).comp x
        ((hasDerivAt_id x).const_sub 1))
    rw [log_mul hx.1.ne' (by linarith [hx.2])]
    convert h using 1 <;> first | rfl | ring
  have hc : ConcaveOn ℝ (Icc 0 (1/2 : ℝ)) g := by
    apply AntitoneOn.concaveOn_of_deriv (convex_Icc _ _)
    · dsimp [g]; fun_prop
    · rw [interior_Icc]
      exact fun x hx => (hd hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx y hy hxy
      rw [(hd hx).deriv, (hd hy).deriv]
      have hp' : x*(1-x) ≤ y*(1-y) := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hxy)
          (show 0 ≤ 1-y-x by linarith [hy.2, hx.2])]
      have hl := log_le_log (mul_pos hx.1 (by linarith [hx.2])) hp'
      linarith
  have hm := hc.min_le_of_mem_Icc (left_mem_Icc.mpr (by norm_num))
    (right_mem_Icc.mpr (by norm_num)) hp
  norm_num [g] at hm
  exact sub_nonneg.mpr hm

theorem binEntropy_le_geometric {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    binEntropy p ≤ 2 * log 2 * sqrt (p*(1-p)) := by
  have half {z : ℝ} (hz : 0 < z) (hz' : z ≤ 1/2) :
      binEntropy z ≤ 2 * log 2 * sqrt (z*(1-z)) := by
    let f := fun x : ℝ => binEntropy x / sqrt (x*(1-x))
    have hpos {x : ℝ} (hx : x ∈ Icc z (1/2 : ℝ)) : 0 < x*(1-x) :=
      mul_pos (hz.trans_le hx.1) (by linarith [hx.2])
    have hd {x : ℝ} (hx : x ∈ Icc z (1/2 : ℝ)) :
        HasDerivAt f (((log (1-x) - log x) * sqrt (x*(1-x)) -
          binEntropy x * ((1-2*x)/(2*sqrt (x*(1-x))))) / (sqrt (x*(1-x)))^2) x := by
      have hq : HasDerivAt (fun y : ℝ => y*(1-y)) (1-2*x) x := by
        convert (hasDerivAt_id x).mul ((hasDerivAt_id x).const_sub 1) using 1 <;> first | rfl | (simp; ring)
      exact (hasDerivAt_binEntropy (hz.trans_le hx.1).ne' (by linarith [hx.2])).div
        (hq.sqrt (hpos hx).ne') (sqrt_pos.mpr (hpos hx)).ne'
    have hmono : MonotoneOn f (Icc z (1/2 : ℝ)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · exact fun x hx => (hd hx).continuousAt.continuousWithinAt
      · exact fun x hx => (hd (interior_subset hx)).differentiableAt.differentiableWithinAt
      · intro x hx
        have hx' := interior_subset hx
        rw [(hd hx').deriv]
        apply div_nonneg _ (sq_nonneg _)
        have hs := entropy_slope_nonneg ⟨(hz.trans_le hx'.1).le, hx'.2⟩
        have hr := sqrt_pos.mpr (hpos hx')
        apply nonneg_of_mul_nonneg_left (b := 2*sqrt (x*(1-x))) _ (by positivity)
        simp only [binEntropy, log_inv, negMulLog] at hs ⊢
        field_simp [hr.ne']
        nlinarith only [hs, congrArg (fun w : ℝ => w*log (1-x)) (sq_sqrt (hpos hx').le),
          congrArg (fun w : ℝ => w*log x) (sq_sqrt (hpos hx').le)]
    have hm := hmono (left_mem_Icc.mpr hz') (right_mem_Icc.mpr hz') hz'
    change binEntropy z / sqrt (z*(1-z)) ≤ binEntropy (1/2) / sqrt ((1/2)*(1-1/2)) at hm
    rw [show (1/2 : ℝ) = 2⁻¹ by norm_num, binEntropy_two_inv] at hm
    norm_num [Real.sqrt_div] at hm
    have bound := (div_le_iff₀ (sqrt_pos.mpr (hpos (left_mem_Icc.mpr hz')))).mp hm
    linarith only [bound]
  rcases hp.eq_or_lt with rfl | hp
  · simp
  rcases hp1.eq_or_lt with rfl | hp1
  · simp
  by_cases h : p ≤ 1/2
  · exact half hp h
  · have hb := half (z := 1-p) (sub_pos.mpr hp1) (by linarith)
    simpa only [binEntropy_one_sub, sub_sub_cancel, mul_comm (1-p) p] using hb

end ThresholdHC.QuantileSelection
