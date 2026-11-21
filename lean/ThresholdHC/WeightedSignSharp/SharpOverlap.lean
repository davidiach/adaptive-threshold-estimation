import ThresholdHC.WeightedSignSharp.Specification
import ThresholdHC.EntropyTailLower.WeightedOverlap

/-! The weighted overlap `∑ⱼ 1_{Eⱼ}/(1+cⱼ) ≤ 25/3` of the actual stopping
windows, on every path, and its integrated form `∑ⱼ e^{-65 cⱼ} ≤ (25/3) e⁸`.
The argument follows `EntropyTailLower.signTest_exponential_overlap`, with the
per-window weight `1/(1+c)` in place of `e^{-c}` and the capped geometric sum
`∑ₙ min(1, 4⁷ 4⁻ⁿ) ≤ 25/3`. No termination under the fair coin is assumed. -/

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.WeightedSignSharp
open ThresholdHC.CriticalEntropy

theorem capped_geometric_sum (M : ℕ) :
    (∑ n ∈ Finset.range M, min 1 (16384 * (1/4 : ℝ)^n)) ≤ 25/3 := by
  have hnn : ∀ n : ℕ, 0 ≤ min 1 (16384 * (1/4 : ℝ)^n) :=
    fun n => le_min zero_le_one (by positivity)
  have hsub : Finset.range M ⊆ Finset.range (7 + M) :=
    Finset.range_subset_range.mpr (by omega)
  calc (∑ n ∈ Finset.range M, min 1 (16384 * (1/4 : ℝ)^n))
      ≤ ∑ n ∈ Finset.range (7 + M), min 1 (16384 * (1/4 : ℝ)^n) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hnn n)
    _ = (∑ n ∈ Finset.range 7, min 1 (16384 * (1/4 : ℝ)^n)) +
          ∑ m ∈ Finset.range M, min 1 (16384 * (1/4 : ℝ)^(7 + m)) :=
        Finset.sum_range_add _ _ _
    _ ≤ (∑ _n ∈ Finset.range 7, (1 : ℝ)) + ∑ m ∈ Finset.range M, (1/4 : ℝ)^m := by
        apply add_le_add
        · exact Finset.sum_le_sum (fun n _ => min_le_left _ _)
        · apply Finset.sum_le_sum
          intro m _
          apply (min_le_right _ _).trans_eq
          rw [pow_add]
          ring
    _ ≤ 7 + 4/3 := by
        apply add_le_add
        · simp
        · have h := geom_sum_mul_of_le_one (by norm_num : (1/4 : ℝ) ≤ 1) M
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/4) M]
    _ = 25/3 := by norm_num

theorem window_overlap_proof : WindowOverlapStatement := by
  intro R _ ν A K d hgap z
  classical
  let cost := fun i : Fin K => (d i : ℝ)^2*
    (expectedSignTestWork ν (signParameter (d i) false) A).toReal
  let events := fun i : Fin K => signTestWindow A (entropyLowerTime (d i))
    (entropyUpperTime (expectedSignTestWork ν (signParameter (d i) false) A).toReal)
  let s := Finset.univ.filter (fun i => z ∈ events i)
  change (∑ i, (events i).indicator (fun _ => 1 / (1 + cost i)) z) ≤ _
  have heq : (∑ i, (events i).indicator (fun _ => 1 / (1 + cost i)) z) =
      ∑ i ∈ s, 1 / (1 + cost i) := by
    simp only [s, Finset.sum_filter, Set.indicator_apply]
  rw [heq]
  by_cases hs : s.Nonempty
  · let j := s.max' hs
    have hj : j ∈ s := s.max'_mem hs
    have hzj : z ∈ events j := (Finset.mem_filter.mp hj).2
    cases hstop : A.stop z with
    | top =>
      have h := hzj.2.2
      rw [hstop] at h
      simp at h
    | coe t =>
      have hbase := (EntropyTailLower.stopping_window_cost ν A (d j) z t hstop hzj).1
      have hi (i : Fin K) (his : i ∈ s) :
          1 / (1 + cost i) ≤ min 1 (16384*(1/4 : ℝ)^(j.val-i.val)) := by
        have hij : i ≤ j := s.le_max' i his
        have hwi := (EntropyTailLower.stopping_window_cost ν A (d i) z t hstop
          (Finset.mem_filter.mp his).2).2
        have hsep := EntropyTailLower.separated_square_gaps d hgap i j hij
        have ht : (0:ℝ) ≤ t := Nat.cast_nonneg _
        have hp : 0 < (4:ℝ)^(j.val-i.val) := by positivity
        have hc : (4:ℝ)^(j.val-i.val)/16384 ≤ cost i := by
          have h₁ := mul_le_mul_of_nonneg_left hsep ht
          have h₂ := mul_le_mul_of_nonneg_left hbase.le hp.le
          dsimp [cost]
          nlinarith
        have hc0 : 0 ≤ cost i := (by positivity : (0:ℝ) ≤ (4:ℝ)^(j.val-i.val)/16384).trans hc
        have hpow : (4:ℝ)^(j.val-i.val)*(1/4:ℝ)^(j.val-i.val) = 1 := by
          rw [← mul_pow]
          norm_num
        have hq : 0 ≤ (1/4:ℝ)^(j.val-i.val) := by positivity
        apply le_min
        · rw [div_le_one (by linarith)]
          linarith
        · rw [div_le_iff₀ (by linarith)]
          have hh := mul_le_mul_of_nonneg_left hc (by positivity :
            (0:ℝ) ≤ 16384*(1/4:ℝ)^(j.val-i.val))
          nlinarith
      have hinj : Set.InjOn (fun i : Fin K => j.val-i.val) (↑s : Set (Fin K)) := by
        intro a ha b hb hab
        have ha' : a.val ≤ j.val := s.le_max' a ha
        have hb' : b.val ≤ j.val := s.le_max' b hb
        change j.val-a.val = j.val-b.val at hab
        apply Fin.ext
        omega
      have hsubset : s.image (fun i : Fin K => j.val-i.val) ⊆ Finset.range (j.val+1) := by
        intro n hn
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hn
        simp only [Finset.mem_range]
        omega
      calc
        _ ≤ ∑ i ∈ s, min 1 (16384*(1/4 : ℝ)^(j.val-i.val)) := Finset.sum_le_sum hi
        _ = ∑ n ∈ s.image (fun i : Fin K => j.val-i.val), min 1 (16384*(1/4:ℝ)^n) := by
          rw [Finset.sum_image hinj]
        _ ≤ ∑ n ∈ Finset.range (j.val+1), min 1 (16384*(1/4:ℝ)^n) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun _ _ _ => le_min zero_le_one (by positivity))
        _ ≤ 25/3 := capped_geometric_sum _
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [he, Finset.sum_empty]
    norm_num

theorem signTest_exponential_sum_sharp {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : SignTest R)
    {K : ℕ} (d : Fin K → EntropyGap)
    (hgap : ∀ i j, j.val = i.val+1 → 2*(d j : ℝ) ≤ (d i : ℝ))
    (hfinite : ∀ i, expectedSignTestWork ν (signParameter (d i) false) A ≠ ∞)
    (herror : ∀ i b, (ν.prod (Tier2.tapeMeasure (signParameter (d i) b))).real
      {z | A.output z ≠ b} ≤ 1/10) :
    (∑ i, exp (-65*((d i : ℝ)^2*
      (expectedSignTestWork ν (signParameter (d i) false) A).toReal))) ≤ 25/3*exp 8 := by
  classical
  let cost := fun i : Fin K => (d i : ℝ)^2*
    (expectedSignTestWork ν (signParameter (d i) false) A).toReal
  let events := fun i : Fin K => signTestWindow A (entropyLowerTime (d i))
    (entropyUpperTime (expectedSignTestWork ν (signParameter (d i) false) A).toReal)
  let P := ν.prod (Tier2.tapeMeasure ⟨1/2,by norm_num⟩)
  have hm (i : Fin K) : MeasurableSet (events i) := measurable_signTestWindow A _ _
  have hi (i : Fin K) : Integrable ((events i).indicator (fun _ => 1 / (1 + cost i))) P :=
    (integrable_const _).indicator (hm i)
  have hbound := integral_mono (integrable_finsetSum Finset.univ (fun i _ => hi i))
    (integrable_const (25/3:ℝ)) (window_overlap_proof ν A K d hgap)
  rw [integral_finsetSum _ (fun i _ => hi i)] at hbound
  have heq (i : Fin K) :
      (∫ z, (events i).indicator (fun _ => 1 / (1 + cost i)) z ∂P) =
        1 / (1 + cost i)*P.real (events i) := by
    rw [integral_indicator_const _ (hm i)]
    simp [smul_eq_mul,mul_comm]
  simp only [heq,integral_const,probReal_univ,one_smul] at hbound
  have hmass (i : Fin K) : exp (-64*cost i-8) ≤ P.real (events i) :=
    signTest_fair_window ν A (d i) (by simpa using herror i false)
      (by simpa using herror i true) (hfinite i)
  have hterm (i : Fin K) : exp (-65*cost i-8) ≤ 1 / (1 + cost i)*P.real (events i) := by
    have hc0 : 0 ≤ cost i := by dsimp [cost]; positivity
    have hexp : exp (-cost i) ≤ 1 / (1 + cost i) := by
      rw [exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (by linarith) (by linarith [add_one_le_exp (cost i)])
    have h := mul_le_mul hexp (hmass i) (exp_pos _).le (div_nonneg zero_le_one (by linarith))
    rw [← exp_add] at h
    convert h using 2
    ring
  have hsum : (∑ i, exp (-65*cost i-8)) ≤ 25/3 :=
    (Finset.sum_le_sum (fun i _ => hterm i)).trans hbound
  have hscale := mul_le_mul_of_nonneg_left hsum (exp_pos (8:ℝ)).le
  rw [Finset.mul_sum] at hscale
  have hs (i : Fin K) : exp 8*exp (-65*cost i-8) = exp (-65*cost i) := by
    rw [← exp_add]
    congr 1
    ring
  simp only [hs] at hscale
  simpa only [mul_comm] using hscale

end ThresholdHC.WeightedSignSharp
