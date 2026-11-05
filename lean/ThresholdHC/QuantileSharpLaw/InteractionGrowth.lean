import ThresholdHC.QuantileSharpLaw.Interaction

noncomputable section
open Real
namespace ThresholdHC.QuantileSharpLaw

theorem log_one_add_le_sqrt {A : ℝ} (hA : 0 ≤ A) : log (1+A) ≤ sqrt A := by
  let f := fun x : ℝ => x-log (1+x^2)
  have hd (x : ℝ) : HasDerivAt f (1-2*x/(1+x^2)) x := by
    have h := (hasDerivAt_id x).sub
      (((hasDerivAt_pow 2 x).const_add 1).log (show 1+x^2 ≠ 0 by positivity))
    convert h using 1
    · funext z
      rfl
    · norm_num
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x _
      rw [(hd x).deriv]
      apply sub_nonneg.mpr
      apply (div_le_one (show 0 < 1+x^2 by positivity)).mpr
      nlinarith only [sq_nonneg (x-1)]
  have h := hm (show (0 : ℝ) ∈ Set.Ici 0 by norm_num) (sqrt_nonneg A) (sqrt_nonneg A)
  simpa [f,sq_sqrt hA] using h

theorem costInteraction_derivative_bound {A x : ℝ} (hA : 0 ≤ A) (hx : 1 ≤ x) :
    log ((A+x)/x) ≤ sqrt A := by
  have hx0 : 0 < x := by linarith
  have harg : (A+x)/x ≤ 1+A := by
    apply (div_le_iff₀ hx0).mpr
    have h := mul_le_mul_of_nonneg_left hx hA
    nlinarith only [h]
  exact (log_le_log (div_pos (add_pos_of_nonneg_of_pos hA hx0) hx0) harg).trans
    (log_one_add_le_sqrt hA)

theorem costInteraction_increment {A B : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) :
    costInteraction A B ≤ costInteraction A 1+(B-1)*sqrt A := by
  have hd : DifferentiableOn ℝ (costInteraction A) (interior (Set.Ici 1)) := by
    rw [interior_Ici]
    exact fun x hx => (costInteraction_hasDerivAt hA
      (lt_trans zero_lt_one (show 1 < x from hx))).differentiableAt.differentiableWithinAt
  have hb : ∀ x ∈ interior (Set.Ici (1 : ℝ)), deriv (costInteraction A) x ≤ sqrt A := by
    intro x hx
    rw [interior_Ici] at hx
    have hx1 : 1 < x := hx
    rw [(costInteraction_hasDerivAt hA (by linarith : 0 < x)).deriv]
    exact costInteraction_derivative_bound hA hx1.le
  have h := (convex_Ici (1 : ℝ)).image_sub_le_mul_sub_of_deriv_le
    (costInteraction_continuous A).continuousOn hd hb 1 (by norm_num) B hB hB
  nlinarith only [h]

end ThresholdHC.QuantileSharpLaw
