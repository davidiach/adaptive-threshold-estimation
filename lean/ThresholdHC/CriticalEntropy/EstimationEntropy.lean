import ThresholdHC.CriticalEntropy.SignReduction
import ThresholdHC.CriticalEntropy.FiniteGap

/-!
A finite-gap entropy lower bound for an observable real-output estimator.
The proof constructs one repeated sign test, proves its error/work bounds,
and invokes statistical sign entropy. No independent-restart axiom is used.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem finite_gap_estimation_entropy {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    (K : ℕ) (d : Fin K → EntropyGap) (hK : 32 ≤ Real.log (K : ℝ))
    (hgap : ∀ i j, j.val = i.val+1 → 2*(d j : ℝ) ≤ (d i : ℝ))
    (n : ℕ) (hn : 0 < n) (M : ℝ) (hnM : 160*M ≤ (n : ℝ))
    (hfinite : ∀ i b, expectedStoppedProcedureWork ν (signParameter (d i) b) A ≠ ∞)
    (hmem : ∀ i b, MemLp id 2
      ((ν.prod (Tier2.tapeMeasure (signParameter (d i) b))).map A.output))
    (hM : ∀ i b, (∫ x : ℝ, x^2
      ∂(ν.prod (Tier2.tapeMeasure (signParameter (d i) b))).map A.output) ≤ M)
    (hminus : ∀ i, (∫ x : ℝ, x
      ∂(ν.prod (Tier2.tapeMeasure (signParameter (d i) false))).map A.output) ≤ 1/8)
    (hplus : ∀ i, 5/8 ≤ (∫ x : ℝ, x
      ∂(ν.prod (Tier2.tapeMeasure (signParameter (d i) true))).map A.output)) :
    (K : ℝ)*Real.log (K : ℝ)/(512*(n : ℝ)) ≤
      ∑ i, (d i : ℝ)^2*(expectedStoppedProcedureWork ν (signParameter (d i) false) A).toReal := by
  let test := repeatedSignTest A n (3/8)
  let seeds := Measure.pi (fun _ : Fin n => ν)
  have hf : ∀ i b, expectedSignTestWork seeds (signParameter (d i) b) test ≠ ∞ := by
    intro i b
    rw [repeated_sign_work ν _ A (hfinite i b) n (3/8)]
    exact ENNReal.mul_ne_top (by simp) (hfinite i b)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : M / ((n : ℝ)*(1/4 : ℝ)^2) ≤ 1/10 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have he : ∀ i b, (seeds.prod (Tier2.tapeMeasure (signParameter (d i) b))).real
      {z | test.output z ≠ b} ≤ 1/10 := by
    intro i b
    cases b with
    | false =>
      exact (repeated_sign_minus_error ν _ A (hfinite i false) (hmem i false)
        n hn (1/4) M (3/8) (by norm_num) (hM i false) (by linarith [hminus i])).trans hb
    | true =>
      exact (repeated_sign_plus_error ν _ A (hfinite i true) (hmem i true)
        n hn (1/4) M (3/8) (by norm_num) (hM i true) (by linarith [hplus i])).trans hb
  have hh := finite_gap_sign_entropy seeds test K d hK hgap hf he
  have hw (i : Fin K) :
      (expectedSignTestWork seeds (signParameter (d i) false) test).toReal =
        (n : ℝ)*(expectedStoppedProcedureWork ν (signParameter (d i) false) A).toReal := by
    rw [repeated_sign_work ν _ A (hfinite i false) n (3/8), ENNReal.toReal_mul,
      ENNReal.toReal_natCast]
  simp_rw [hw] at hh
  have hs : (∑ i, (d i : ℝ)^2*((n : ℝ)*
      (expectedStoppedProcedureWork ν (signParameter (d i) false) A).toReal)) =
      (n : ℝ)*∑ i, (d i : ℝ)^2*
        (expectedStoppedProcedureWork ν (signParameter (d i) false) A).toReal := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs] at hh
  rw [← div_div, div_le_iff₀ hn']
  simpa only [mul_comm] using hh

theorem critical_restart_count_bounds (r : ℝ) (hr : 2/3 ≤ r) :
    0 < ⌈512*(1+r)⌉₊ ∧
      160*(1/64+2*r) ≤ (⌈512*(1+r)⌉₊ : ℝ) ∧
      (⌈512*(1+r)⌉₊ : ℝ) ≤ 1282*r := by
  have hlo := Nat.le_ceil (512*(1+r))
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ 512*(1+r) by linarith)
  constructor
  · have hp : (0 : ℝ) < ⌈512*(1+r)⌉₊ := by linarith
    exact_mod_cast hp
  constructor <;> nlinarith

end ThresholdHC.CriticalEntropy
