import ThresholdHC.EntropyTailLower.WeightedSign
import ThresholdHC.CriticalEntropy.SignReduction

/-! Weighted entropy lower bounds for actual observable real-valued
single-coin procedures. Independent restarts use fresh blocks of the same
coin's tape, and their observation costs are proved to add. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.CriticalEntropy

theorem weighted_estimation_entropy {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    (K : ℕ) (d : Fin K → EntropyGap)
    (hgap : ∀ i j, j.val = i.val+1 → 2*(d j : ℝ) ≤ (d i : ℝ))
    (n : ℕ) (hn : 0 < n) (M threshold margin : ℝ) (hmargin : 0 < margin)
    (hnM : 10*M ≤ (n:ℝ)*margin^2)
    (hfinite : ∀ i b, expectedStoppedProcedureWork ν (signParameter (d i) b) A ≠ ∞)
    (hmem : ∀ i b, MemLp id 2
      ((ν.prod (Tier2.tapeMeasure (signParameter (d i) b))).map A.output))
    (hM : ∀ i b, (∫ x : ℝ, x^2
      ∂(ν.prod (Tier2.tapeMeasure (signParameter (d i) b))).map A.output) ≤ M)
    (hminus : ∀ i, (∫ x : ℝ, x
      ∂(ν.prod (Tier2.tapeMeasure (signParameter (d i) false))).map A.output) ≤ threshold-margin)
    (hplus : ∀ i, threshold+margin ≤ (∫ x : ℝ, x
      ∂(ν.prod (Tier2.tapeMeasure (signParameter (d i) true))).map A.output))
    (a : Fin K → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ThresholdHC.EntropyTailQuantile.costEntropy a ≤
      4096*(n:ℝ)*∑ i, a i*((d i:ℝ)^2*
        (expectedStoppedProcedureWork ν (signParameter (d i) false) A).toReal) := by
  let test := repeatedSignTest A n threshold
  let seeds := Measure.pi (fun _ : Fin n => ν)
  have hf (i : Fin K) : expectedSignTestWork seeds (signParameter (d i) false) test ≠ ∞ := by
    rw [repeated_sign_work ν _ A (hfinite i false) n threshold]
    exact ENNReal.mul_ne_top (by simp) (hfinite i false)
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hb : M/((n:ℝ)*margin^2) ≤ 1/10 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have he : ∀ i b, (seeds.prod (Tier2.tapeMeasure (signParameter (d i) b))).real
      {z | test.output z ≠ b} ≤ 1/10 := by
    intro i b
    cases b with
    | false =>
      exact (repeated_sign_minus_error ν _ A (hfinite i false) (hmem i false)
        n hn margin M threshold hmargin (hM i false) (by linarith [hminus i])).trans hb
    | true =>
      exact (repeated_sign_plus_error ν _ A (hfinite i true) (hmem i true)
        n hn margin M threshold hmargin (hM i true) (by linarith [hplus i])).trans hb
  have hh := weighted_sign_entropy seeds test K d hgap hf he a ha
  have hw (i : Fin K) :
      (expectedSignTestWork seeds (signParameter (d i) false) test).toReal =
        (n:ℝ)*(expectedStoppedProcedureWork ν (signParameter (d i) false) A).toReal := by
    rw [repeated_sign_work ν _ A (hfinite i false) n threshold, ENNReal.toReal_mul,
      ENNReal.toReal_natCast]
  simp_rw [hw] at hh
  convert hh using 1
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end ThresholdHC.EntropyTailLower
