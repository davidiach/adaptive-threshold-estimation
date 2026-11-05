import ThresholdHC.FiniteCapTruncation.Tail

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.FiniteCapTruncation
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram

def capCertificate {M : ℕ} (N : ℕ) (B : ℝ) (C : Certificate M) : Certificate N :=
  ⟨capFlow N C.flow, C.offset,
    C.bias + Real.sqrt (B*C.variance/((N:ℝ)+1)), C.variance⟩

theorem capCertificate_feasible {M N : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ} (hB : 0 ≤ B)
    (C : Certificate M) (hC : Feasible μ ρ B C) :
    Feasible μ ρ B (capCertificate N B C) := by
  refine ⟨capFlow_cone hN hNM C.flow hC.cone,
    add_nonneg hC.bias_nonneg (Real.sqrt_nonneg _), hC.variance_nonneg, ?_, ?_, ?_⟩
  · intro q hq
    have hsplit := countMean_split hNM μ q C.flow.outputWeight
    have htail := discarded_output_bound μ q N C.flow hC.cone hB hC.variance_nonneg
      (hC.work_bound q hq) (hC.variance_bound q hq)
    change |C.offset + countMean μ q (fun s : CountState N =>
      arrayAt C.flow.outputWeight s.1.val s.2.val) - signMean μ q.val| ≤
      C.bias + Real.sqrt (B*C.variance/((N:ℝ)+1))
    calc
      _ = |(C.offset+countMean μ q C.flow.outputWeight-signMean μ q.val) -
          discardedMean μ q N C.flow.outputWeight| := by congr 1; linarith
      _ ≤ |C.offset+countMean μ q C.flow.outputWeight-signMean μ q.val| +
          |discardedMean μ q N C.flow.outputWeight| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (C.offset+countMean μ q C.flow.outputWeight-signMean μ q.val)
            (-discardedMean μ q N C.flow.outputWeight)
      _ ≤ _ := add_le_add (hC.bias_bound q hq) htail
  · intro q hq
    exact (capFlow_moment_le hNM μ q C.flow hC.cone).trans (hC.variance_bound q hq)
  · intro q hq
    exact (capFlow_work_le hNM μ q C.flow hC.cone).trans (hC.work_bound q hq)

/-- The bias increment is at most a square-root fraction of the original
RMS certificate; no lower bound on the gap or rarity is used. -/
theorem capCertificate_squared {M : ℕ} (N : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (C : Certificate M) (hV : 0 ≤ C.variance) :
    certificateSquared (capCertificate N B C) ≤
      ENNReal.ofReal ((1+Real.sqrt (B/((N:ℝ)+1)))^2) * certificateSquared C := by
  let t := Real.sqrt (B/((N:ℝ)+1))
  let u := Real.sqrt C.variance
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hu : u^2 = C.variance := Real.sq_sqrt hV
  have he : Real.sqrt (B*C.variance/((N:ℝ)+1)) = t*u := by
    rw [show B*C.variance/((N:ℝ)+1) = (B/((N:ℝ)+1))*C.variance by ring,
      Real.sqrt_mul (div_nonneg hB (by positivity))]
  have hs : (C.bias+t*u)^2+C.variance ≤ (1+t)^2*(C.bias^2+C.variance) := by
    rw [← hu]
    nlinarith [mul_nonneg ht (sq_nonneg (C.bias-u)),
      mul_nonneg ht (add_nonneg (sq_nonneg C.bias) (sq_nonneg u)), sq_nonneg (t*C.bias)]
  rw [certificateSquared, certificateSquared, ← ENNReal.ofReal_mul (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [capCertificate, he] using hs

end ThresholdHC.FiniteCapTruncation

