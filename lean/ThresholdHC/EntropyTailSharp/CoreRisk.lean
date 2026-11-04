import ThresholdHC.EntropyTailSharp.Core
import ThresholdHC.FiniteQuantile.CoreRisk

/-! Explicit transport from the sharpened finite-certificate price to the observable minimax risk. -/
noncomputable section
open MeasureTheory Set Real
open scoped BigOperators ENNReal
namespace ThresholdHC.EntropyTailSharp
open ThresholdHC.FiniteQuantile ThresholdHC.EntropyTailLower ThresholdHC.EntropyTailQuantile
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.RareAboveTwo

theorem annular_root_constant_sharp :
    256 + sqrt (16384 * exp 48) ≤ (6:ℝ)*10^12 := by
  have he1 : exp 1 ≤ 11/4 := by linarith only [exp_one_lt_d9]
  have he24 : exp 24 ≤ 40000000000 := by
    calc
      _ = exp 1 ^ 24 := by rw [← exp_nat_mul]; norm_num
      _ ≤ (11/4:ℝ)^24 := pow_le_pow_left₀ (exp_pos _).le he1 _
      _ ≤ _ := by norm_num
  have he : exp 48 = exp 24 * exp 24 := by rw [← exp_add]; norm_num
  rw [he, show (16384:ℝ)*(exp 24*exp 24) = (128*exp 24)^2 by ring,
    sqrt_sq (show 0 ≤ 128*exp 24 by positivity)]
  linarith only [he24]

theorem certificate_root_bound_sharp {N : ℕ} (C : Certificate N)
    (hv : 0 ≤ C.variance) :
    256*C.bias + sqrt ((16384*exp 48)*C.variance) ≤
      (6*10^12)*sqrt (C.bias^2+C.variance) := by
  have hbr : C.bias ≤ sqrt (C.bias^2+C.variance) := le_sqrt_of_sq_le (by linarith only [hv])
  have hvr : sqrt C.variance ≤ sqrt (C.bias^2+C.variance) :=
    sqrt_le_sqrt (by linarith only [sq_nonneg C.bias])
  rw [sqrt_mul (by positivity : 0 ≤ (16384:ℝ)*exp 48)]
  nlinarith only [mul_le_mul_of_nonneg_left hvr (sqrt_nonneg (16384*exp 48)),
    hbr, mul_le_mul_of_nonneg_right annular_root_constant_sharp (sqrt_nonneg (C.bias^2+C.variance))]

theorem core_observable_bound_sharp {n : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B t : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (ht : 0 < t)
    (hbefore : ∀ j < n, t ≤ bandEdge j)
    (hlarge : 262144 < prefixCoreEntropy μ n)
    (hcut : 32*(65536*(sqrt ρ/sqrt (prefixCoreEntropy μ n))) ≤ t) :
    min ρ (sqrt (ρ*prefixCoreEntropy μ n/B)) ≤
      (3*10^16)*(rareMinimaxRisk μ ρ B).toReal := by
  let N := certificateCap ρ B
  obtain ⟨C,hC,he⟩ := programSquared_attained N μ hρ (by linarith) hB.le
  have hp := filtered_prefix_certificate_sharp μ hρ hB ht hbefore (certificateCap_pos ρ B hB)
    C hC hlarge hcut
  have hr := certificate_root_bound_sharp C hC.variance_nonneg
  have hRn : rareMinimaxRisk μ ρ B ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (EntropyTailExecution.minimax_half_rarity μ hρ.le)
  have hprog := (finite_certificate μ ρ B hρ hρ4 hB).2
  have heq : ENNReal.ofReal (sqrt (C.bias^2+C.variance)) = programValue μ ρ B N := by
    rw [programValue, ← he, certificateSquared, ENNReal.ofReal_rpow_of_nonneg
      (by positivity [hC.variance_nonneg]) (by norm_num), ← sqrt_eq_rpow]
  change programValue μ ρ B N ≤ 16*rareMinimaxRisk μ ρ B at hprog
  rw [← heq] at hprog
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num : (16:ℝ≥0∞) ≠ ⊤) hRn) hprog
  rw [ENNReal.toReal_ofReal (sqrt_nonneg _), ENNReal.toReal_mul] at hh
  norm_num only [ENNReal.toReal_ofNat] at hh
  nlinarith only [hp, hr, hh, ENNReal.toReal_nonneg (a := rareMinimaxRisk μ ρ B)]

end ThresholdHC.EntropyTailSharp
