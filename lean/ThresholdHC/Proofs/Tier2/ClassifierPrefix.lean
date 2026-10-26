import ThresholdHC.Proofs.Tier2.ClassifierProbability
import ThresholdHC.Proofs.Tier2.ClassifierBridge
import ThresholdHC.Proofs.Tier2.ClassifierModel

noncomputable section
open MeasureTheory ProbabilityTheory Real
namespace ThresholdHC.Tier2
open Uniform713

theorem succCount_prefix_eq_sum {M n : ℕ} (hn : n ≤ M) (ω : ℕ → Bool) :
    (succCount (tapePrefix M ω) n : ℝ) = ∑ i ∈ Finset.range n, observations i ω := by
  have hc : (succCount (tapePrefix M ω) n : ℝ) =
      ∑ i : Fin M, if i.val < n ∧ ω i.val = true then (1:ℝ) else 0 := by
    simp only [succCount, tapePrefix, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    exact Finset.sum_filter (s := Finset.univ) (fun i : Fin M => i.val < n ∧ ω i.val = true) (fun _ => (1:ℝ))
  rw [hc]
  calc
    _ = ∑ i ∈ Finset.range M, if i < n then bit (ω i) else 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : i.val < n <;> cases hb : ω i.val <;> simp [h, bit]
    _ = ∑ i ∈ Finset.range n, if i < n then bit (ω i) else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hn)
      intro i hi hin
      simp only [Finset.mem_range] at hin
      simp [hin]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi, observations]

theorem finiteMean_prefix {M j : ℕ} (hj : 2^j ≤ M) (ω : ℕ → Bool) :
    finiteMean (tapePrefix M ω) j = dyadicMean observations j ω := by
  unfold finiteMean dyadicMean prefixMean
  rw [succCount_prefix_eq_sum hj]
  norm_cast

theorem boundary_eq_model : boundary = fun k L => Model.threshold1 (cap k) (cap L) := by
  funext k L
  simp [boundary, finiteBoundary, thrK, Model.threshold1, cap]

theorem firstStop_congr_prefix (b : ℕ → ℕ → ℝ) (m m' : ℕ → ℝ) (L : ℕ)
    (hm : ∀ k ≤ L, m k = m' k) : firstStop b m L = firstStop b m' L := by
  apply (firstStop_eq_iff b m L _).2
  have hs := firstStop_le b m' L
  constructor
  · simpa only [hm _ hs] using firstStop_spec b m' L
  · intro k hk
    have h := firstStop_min b m' L k hk
    simpa only [hm k h.1.le] using h

theorem firstDecision_congr_prefix (b : ℕ → ℕ → ℝ) (m m' : ℕ → ℝ) (L : ℕ)
    (hm : ∀ k ≤ L, m k = m' k) : firstDecision b m L = firstDecision b m' L := by
  unfold firstDecision
  rw [firstStop_congr_prefix b m m' L hm, hm _ (firstStop_le b m' L)]

theorem zK_prefix (L : ℕ) {M : ℕ} (hM : 2^L ≤ M) (ω : ℕ → Bool) :
    zK 1 1 L (tapePrefix M ω) = Model.decision (fun j => dyadicMean observations j ω) L := by
  rw [zK_eq_firstDecision]
  change firstDecision boundary _ _ = _
  rw [boundary_eq_model]
  apply firstDecision_congr_prefix
  intro k hk
  exact finiteMean_prefix ((Nat.pow_le_pow_right (by omega : 0 < 2) hk).trans hM) ω

theorem classifyK_work_prefix (L : ℕ) {M : ℕ} (hM : 2^L ≤ M) (ω : ℕ → Bool) :
    ((classifyK 1 1 L (tapePrefix M ω)).2 : ℝ) =
      Model.work (fun j => dyadicMean observations j ω) L := by
  rw [classifyK_work_eq_cap]
  change cap (firstStop boundary _ _) = _
  rw [boundary_eq_model]
  apply congrArg cap
  apply firstStop_congr_prefix
  intro k hk
  exact finiteMean_prefix ((Nat.pow_le_pow_right (by omega : 0 < 2) hk).trans hM) ω

end ThresholdHC.Tier2
