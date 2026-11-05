import ThresholdHC.FiniteCapTruncation.Certificate
import ThresholdHC.Genie.CapMonotonicity
import ThresholdHC.Genie.Model

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.FiniteCapTruncation
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.Genie

theorem programSquared_cap_le {M N : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    programSquared μ ρ B N ≤
      ENNReal.ofReal ((1+Real.sqrt (B/((N:ℝ)+1)))^2) * programSquared μ ρ B M := by
  let c := ENNReal.ofReal ((1+Real.sqrt (B/((N:ℝ)+1)))^2)
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hc' : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdiv : programSquared μ ρ B N / c ≤ programSquared μ ρ B M := by
    apply le_sInf
    rintro x ⟨C,hC,rfl⟩
    apply (ENNReal.div_le_iff hc hc').mpr
    have hf := capCertificate_feasible hN hNM μ hB C hC
    have hle : programSquared μ ρ B N ≤ certificateSquared (capCertificate N B C) :=
      sInf_le ⟨capCertificate N B C, hf, rfl⟩
    simpa only [mul_comm] using hle.trans (capCertificate_squared N hB C hC.variance_nonneg)
  simpa only [mul_comm] using (ENNReal.div_le_iff hc hc').mp hdiv

theorem programValue_cap_le {M N : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    programValue μ ρ B N ≤
      ENNReal.ofReal (1+Real.sqrt (B/((N:ℝ)+1))) * programValue μ ρ B M := by
  have h := ENNReal.rpow_le_rpow (programSquared_cap_le hN hNM μ ρ hB)
    (show (0:ℝ) ≤ 1/2 by norm_num)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.ofReal_pow (by positivity : 0 ≤ 1+Real.sqrt (B/((N:ℝ)+1))),
    ← ENNReal.rpow_natCast_mul] at h
  norm_num at h
  exact h

/-- A square-root relative convergence rate for the ordinary optimized cap
program. This compares P_N with P_infinity, not with the genie lower program. -/
theorem ordinary_cap_rate (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) {B : ℝ} (hB : 0 ≤ B) (N : ℕ) (hN : 0 < N) :
    infiniteProgramValue μ ρ B ≤ programValue μ ρ B N ∧
      programValue μ ρ B N ≤
        ENNReal.ofReal (1+Real.sqrt (B/((N:ℝ)+1))) * infiniteProgramValue μ ρ B := by
  constructor
  · have he : N-1+1 = N := Nat.sub_add_cancel (Nat.succ_le_of_lt hN)
    simpa only [infiniteProgramValue, he] using
      iInf_le (fun n : ℕ => programValue μ ρ B (n+1)) (N-1)
  · let c := ENNReal.ofReal (1+Real.sqrt (B/((N:ℝ)+1)))
    have hc : c ≠ 0 := by dsimp [c]; positivity
    have hc' : c ≠ ⊤ := ENNReal.ofReal_ne_top
    change programValue μ ρ B N ≤ c * ⨅ m : ℕ, programValue μ ρ B (m+1)
    rw [ENNReal.mul_iInf_of_ne hc hc']
    apply le_iInf
    intro m
    by_cases hNm : N ≤ m+1
    · exact programValue_cap_le hN hNm μ ρ hB
    · have hle := programValue_antitone μ ρ B (le_of_not_ge hNm)
      have hfactor : (1:ℝ≥0∞) ≤ c := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (Real.sqrt_nonneg _))
      have hscale := mul_le_mul_right hfactor (programValue μ ρ B (m+1))
      exact hle.trans (by simpa only [one_mul, mul_one, mul_comm] using hscale)

end ThresholdHC.FiniteCapTruncation

