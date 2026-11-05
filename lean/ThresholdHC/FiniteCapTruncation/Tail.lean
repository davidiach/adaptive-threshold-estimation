import ThresholdHC.FiniteCapTruncation.Flow
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ThresholdHC.FiniteCapTruncation
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.Genie

def discardedMean {M : ℕ} (μ : Measure Gap) (q : SignLaw) (N : ℕ)
    (u : CountState M → ℝ) : ℝ :=
  ∑ s ∈ (Finset.univ.filter fun s : CountState M => N < s.1.val),
    countCoefficient μ q s * u s

theorem discardedMean_nonneg {M : ℕ} (μ : Measure Gap) (q : SignLaw) (N : ℕ)
    (u : CountState M → ℝ) (hu : ∀ s, 0 ≤ u s) : 0 ≤ discardedMean μ q N u :=
  Finset.sum_nonneg fun s _ => mul_nonneg (countCoefficient_nonneg μ q s) (hu s)

theorem discardedMean_le {M : ℕ} (μ : Measure Gap) (q : SignLaw) (N : ℕ)
    (u : CountState M → ℝ) (hu : ∀ s, 0 ≤ u s) :
    discardedMean μ q N u ≤ countMean μ q u :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun s _ _ => mul_nonneg (countCoefficient_nonneg μ q s) (hu s))

theorem countMean_split {M N : ℕ} (hNM : N ≤ M) (μ : Measure Gap)
    (q : SignLaw) (u : CountState M → ℝ) :
    countMean μ q (fun s : CountState N => arrayAt u s.1.val s.2.val) +
      discardedMean μ q N u = countMean μ q u := by
  rw [kept_countMean hNM]
  simp only [discardedMean, countMean, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hn : s.1.val ≤ N
  · simp [hn, Nat.not_lt.mpr hn]
  · simp [hn, Nat.lt_of_not_ge hn]

theorem capFlow_moment_le {M N : ℕ} (hNM : N ≤ M) (μ : Measure Gap)
    (q : SignLaw) (f : Flow M) (hf : FlowCone f) :
    countMean μ q (capFlow N f).momentWeight ≤ countMean μ q f.momentWeight := by
  have h := countMean_split hNM μ q f.momentWeight
  have hn := discardedMean_nonneg μ q N f.momentWeight hf.moment_nonneg
  change countMean μ q (fun s : CountState N =>
    arrayAt f.momentWeight s.1.val s.2.val) ≤ _
  linarith

/-- A discarded stop uses at least N+1 paid observations. The root intensity
need not be one: this estimate applies directly to feasible conic certificates. -/
theorem discarded_mass_work {M : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (N : ℕ) (f : Flow M) (hf : FlowCone f) :
    ((N:ℝ)+1) * discardedMean μ q N f.stopWeight ≤
      countMean μ q f.continueWeight := by
  rw [← flow_work_stopping_depth μ q f hf]
  unfold discardedMean
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ s ∈ (Finset.univ.filter fun s : CountState M => N < s.1.val),
        countCoefficient μ q s * ((s.1.val:ℝ) * f.stopWeight s) := by
      apply Finset.sum_le_sum
      intro s hs
      have hdepth : (N:ℝ)+1 ≤ s.1.val := by
        exact_mod_cast Nat.succ_le_of_lt (Finset.mem_filter.mp hs).2
      have hweight := mul_nonneg (countCoefficient_nonneg μ q s) (hf.stop_nonneg s)
      nlinarith [mul_le_mul_of_nonneg_right hdepth hweight]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun s _ _ => mul_nonneg (countCoefficient_nonneg μ q s)
        (mul_nonneg (Nat.cast_nonneg _) (hf.stop_nonneg s)))

theorem discarded_output_sq {M : ℕ} (μ : Measure Gap) (q : SignLaw)
    (N : ℕ) (f : Flow M) (hf : FlowCone f) :
    (discardedMean μ q N f.outputWeight)^2 ≤
      discardedMean μ q N f.stopWeight * discardedMean μ q N f.momentWeight := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro s _
    exact mul_nonneg (countCoefficient_nonneg μ q s) (hf.stop_nonneg s)
  · intro s _
    exact mul_nonneg (countCoefficient_nonneg μ q s) (hf.moment_nonneg s)
  · intro s _
    calc
      (countCoefficient μ q s * f.outputWeight s)^2 =
          (countCoefficient μ q s)^2 * (f.outputWeight s)^2 := mul_pow _ _ _
      _ ≤ (countCoefficient μ q s)^2 * (f.stopWeight s * f.momentWeight s) :=
        mul_le_mul_of_nonneg_left (hf.perspective s) (sq_nonneg _)
      _ = _ := by ring

theorem discarded_output_bound {M : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (N : ℕ) (f : Flow M) (hf : FlowCone f)
    {B V : ℝ} (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hw : countMean μ q f.continueWeight ≤ B)
    (hv : countMean μ q f.momentWeight ≤ V) :
    |discardedMean μ q N f.outputWeight| ≤ Real.sqrt (B*V/((N:ℝ)+1)) := by
  have hn : 0 < (N:ℝ)+1 := by positivity
  have hm : discardedMean μ q N f.stopWeight ≤ B/((N:ℝ)+1) := by
    apply (le_div_iff₀ hn).mpr
    simpa only [mul_comm] using (discarded_mass_work μ q N f hf).trans hw
  have hmoment := (discardedMean_le μ q N f.momentWeight hf.moment_nonneg).trans hv
  have hsq := (discarded_output_sq μ q N f hf).trans
    (mul_le_mul hm hmoment (discardedMean_nonneg μ q N f.momentWeight hf.moment_nonneg)
      (div_nonneg hB hn.le))
  have he : B/((N:ℝ)+1)*V = B*V/((N:ℝ)+1) := by ring
  rw [he] at hsq
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt (div_nonneg (mul_nonneg hB hV) hn.le)]
  exact hsq

end ThresholdHC.FiniteCapTruncation

