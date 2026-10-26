import ThresholdHC.Uniform713.Common

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ThresholdHC.Uniform713

/-- Every fixed inverse-square dyadic error envelope tends to zero. -/
theorem tendsto_dyadic_error_zero (C d : ℝ) :
    Tendsto (fun L => C / (cap L*d^2)^2) atTop (𝓝 0) := by
  have hgeom := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0:ℝ) ≤ 1/4 by norm_num) (show (1/4:ℝ) < 1 by norm_num)
  have h := hgeom.const_mul (C/d^4)
  convert h using 1
  · ext L
    unfold cap
    rw [mul_pow, div_mul_eq_div_div]
    have hpow : ((2:ℝ)^L)^2 = (4:ℝ)^L := by
      rw [← pow_mul, Nat.mul_comm L 2, pow_mul]
      norm_num
    rw [hpow]
    simp only [div_eq_mul_inv, ← inv_pow]
    ring
  · simp

/-- The proved classifier error envelope vanishes at every positive gap. -/
theorem tendsto_errorEnvelope_zero (d : ℝ) (hd : 0 < d) :
    Tendsto (fun L => errorPrefactor / (cap L*d^2)^2) atTop (𝓝 0) :=
  tendsto_dyadic_error_zero errorPrefactor d

/-- A nonnegative sequence dominated by the classifier error envelope vanishes. -/
theorem tendsto_of_error_envelope {e : ℕ → ℝ} (d : ℝ) (hd : 0 < d)
    (he0 : ∀ L, 0 ≤ e L)
    (he : ∀ L, e L ≤ errorPrefactor / (cap L*d^2)^2) :
    Tendsto e atTop (𝓝 0) :=
  squeeze_zero he0 he (tendsto_errorEnvelope_zero d hd)

/-- In particular, classifier error probabilities bounded by this envelope vanish. -/
theorem tendsto_error_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (events : ℕ → Set Ω) (d : ℝ) (hd : 0 < d)
    (he : ∀ L, μ.real (events L) ≤ errorPrefactor / (cap L*d^2)^2) :
    Tendsto (fun L => μ.real (events L)) atTop (𝓝 0) := by
  apply tendsto_of_error_envelope d hd _ he
  intro L
  exact measureReal_nonneg

end ThresholdHC.Uniform713

#print axioms ThresholdHC.Uniform713.tendsto_dyadic_error_zero
#print axioms ThresholdHC.Uniform713.tendsto_errorEnvelope_zero
#print axioms ThresholdHC.Uniform713.tendsto_of_error_envelope
#print axioms ThresholdHC.Uniform713.tendsto_error_probability
