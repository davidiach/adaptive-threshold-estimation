import ThresholdHC.ConfidenceProgram.Lower
import ThresholdHC.Genie.OptimizedConvergence

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.ConfidenceEntropy
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram
open ThresholdHC.EntropyTailLower ThresholdHC.EntropyTailSharp ThresholdHC.Genie
open ThresholdHC.FiniteQuantile ThresholdHC.EntropyTailQuantile

/-- Compare the retained entropy directly with every finite stopping program,
then take its cap infimum. -/
theorem core_program_bound {n : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B t : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (ht : 0 < t)
    (hbefore : ∀ j < n, t ≤ bandEdge j)
    (hlarge : 262144 < prefixCoreEntropy μ n)
    (hcut : 32*(65536*(sqrt ρ/sqrt (prefixCoreEntropy μ n))) ≤ t) :
    min ρ (sqrt (ρ*prefixCoreEntropy μ n/B)) ≤
      (16*10^14)*(infiniteProgramValue μ ρ B).toReal := by
  let M := min ρ (sqrt (ρ*prefixCoreEntropy μ n/B))
  have hM : 0 ≤ M := le_min hρ.le (sqrt_nonneg _)
  have hbound : ENNReal.ofReal (M/(16*10^14)) ≤ infiniteProgramValue μ ρ B := by
    unfold infiniteProgramValue
    apply le_iInf
    intro N
    obtain ⟨C,hC,he⟩ := programSquared_attained (N+1) μ hρ (by linarith) hB.le
    have hp := filtered_prefix_certificate_sharp μ hρ hB ht hbefore (Nat.succ_pos N)
      C hC hlarge hcut
    have hr := certificate_root_bound_sharp C hC.variance_nonneg
    have heq : ENNReal.ofReal (sqrt (C.bias^2+C.variance)) = programValue μ ρ B (N+1) := by
      rw [programValue,← he,certificateSquared,ENNReal.ofReal_rpow_of_nonneg
        (by positivity [hC.variance_nonneg]) (by norm_num),← sqrt_eq_rpow]
    rw [← heq]
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 16*10^14)).mpr
    change M ≤ 256*(256*C.bias+sqrt ((16384*exp 48)*C.variance)) at hp
    nlinarith only [hp,hr,sqrt_nonneg (C.bias^2+C.variance)]
  have h := ENNReal.toReal_mono (infiniteProgramValue_ne_top μ hρ.le hB.le) hbound
  rw [ENNReal.toReal_ofReal (div_nonneg hM (by norm_num))] at h
  calc
    _ ≤ (infiniteProgramValue μ ρ B).toReal*(16*10^14) :=
      (div_le_iff₀ (by norm_num : (0 : ℝ) < 16*10^14)).mp h
    _ = _ := mul_comm _ _

end ThresholdHC.ConfidenceEntropy
