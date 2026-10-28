import ThresholdHC.Confidence.Median
import Mathlib

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.Confidence

/-- A finite union bound over all majority subsets gives exponential confidence
amplification. Independence concerns only the real-valued outputs. -/
theorem median_failure_bound {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (m : ℕ) (f : MedianIndex m → Ω → ℝ)
    (hind : iIndepFun f P) (θ r : ℝ)
    (hfail : ∀ i, P {z | r < |f i z-θ|} ≤ (1/8 : ℝ≥0∞)) :
    P {z | r < |median m (fun i => f i z)-θ|} ≤ (1/2 : ℝ≥0∞)^m := by
  classical
  let C : MedianSet m → Set Ω := fun s => ⋂ i ∈ s.val, {z | r < |f i z-θ|}
  have hC (s : MedianSet m) : P (C s) ≤ (1/8 : ℝ≥0∞)^(m+1) := by
    have hi : P (C s) = ∏ i ∈ s.val, P {z | r < |f i z-θ|} := by
      apply hind.meas_biInter
      intro i _
      exact ⟨{x : ℝ | r < |x-θ|},
        measurableSet_lt measurable_const ((measurable_id.sub_const θ).abs), rfl⟩
    rw [hi]
    calc
      _ ≤ ∏ _i ∈ s.val, (1/8 : ℝ≥0∞) := Finset.prod_le_prod' (fun i _ => hfail i)
      _ = (1/8 : ℝ≥0∞)^(m+1) := by simp [s.property]
  have hsub : {z | r < |median m (fun i => f i z)-θ|} ⊆ ⋃ s, C s := by
    intro z hz
    obtain ⟨s,hs⟩ := median_bad_subset m (fun i => f i z) θ r hz
    apply Set.mem_iUnion.mpr
    exact ⟨s, by simpa only [C, Set.mem_iInter, Set.mem_setOf_eq] using hs⟩
  calc
    _ ≤ P (⋃ s, C s) := measure_mono hsub
    _ ≤ ∑ s : MedianSet m, P (C s) := measure_iUnion_fintype_le P C
    _ ≤ ∑ _s : MedianSet m, (1/8 : ℝ≥0∞)^(m+1) := Finset.sum_le_sum (fun s _ => hC s)
    _ = (Fintype.card (MedianSet m) : ℝ≥0∞) * (1/8 : ℝ≥0∞)^(m+1) := by simp [nsmul_eq_mul]
    _ ≤ (2 : ℝ≥0∞)^(2*m+1) * (1/8 : ℝ≥0∞)^(m+1) := by
      gcongr
      exact_mod_cast medianSet_card_le m
    _ = ((2 : ℝ≥0∞)^2 * (1/8))^m * (2*(1/8)) := by
      simp only [pow_add, pow_one, pow_mul, pow_succ, mul_pow, pow_zero, one_pow, mul_one, one_mul]
      ac_rfl
    _ = (1/2 : ℝ≥0∞)^m * (1/4) := by
      rw [show (2 : ℝ≥0∞)^2 * (1/8) = 1/2 by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num,
        show (2 : ℝ≥0∞)*(1/8) = 1/4 by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num]
    _ ≤ (1/2 : ℝ≥0∞)^m * 1 := mul_le_mul le_rfl (by norm_num) bot_le bot_le
    _ = (1/2 : ℝ≥0∞)^m := mul_one _

end ThresholdHC.Confidence
