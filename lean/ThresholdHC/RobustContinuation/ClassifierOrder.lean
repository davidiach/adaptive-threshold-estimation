import ThresholdHC.RobustContinuation.TapeOrder
import ThresholdHC.BlindUpper.ClassifierProcedure

/-! The ordinary classifier is monotone in the flips.

The classifier stops at the first check where the running mean leaves the
band around `1/2`, or at the terminal check, and decides positive when the
mean at its stop exceeds `1/2`; a terminal tie is negative. When every mean
is raised, a positive decision stays positive and is not delayed, and a stop
that comes strictly earlier is a positive decision. The statements are for
every boundary sequence. -/

noncomputable section
open MeasureTheory Set

namespace ThresholdHC.RobustContinuation
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Uniform713 ThresholdHC.BlindUpper

/-- A positive decision reads a mean above `1/2` at its stop. -/
theorem half_lt_of_firstDecision_one (b : ℕ → ℕ → ℝ) (m : ℕ → ℝ) (L : ℕ)
    (hd : firstDecision b m L = 1) : 1/2 < m (firstStop b m L) := by
  by_contra hc
  unfold firstDecision at hd
  simp only [hc, ite_false] at hd
  exact zero_ne_one hd

/-- Raising the means does not delay a positive decision. -/
theorem firstStop_le_of_decision_one (b : ℕ → ℕ → ℝ) {m m' : ℕ → ℝ} (h : ∀ k, m k ≤ m' k)
    (L : ℕ) (hd : firstDecision b m L = 1) : firstStop b m' L ≤ firstStop b m L := by
  have hm := half_lt_of_firstDecision_one b m L hd
  rcases firstStop_spec b m L with hL | hcross
  · exact (firstStop_le b m' L).trans hL
  · apply firstStop_le_of_cross
    rw [abs_of_pos (by linarith)] at hcross
    exact hcross.trans_le ((sub_le_sub_right (h _) _).trans (le_abs_self _))

/-- With raised means, a strictly earlier stop is a positive decision. -/
theorem firstDecision_one_of_stop_lt (b : ℕ → ℕ → ℝ) {m m' : ℕ → ℝ} (h : ∀ k, m k ≤ m' k)
    (L : ℕ) (hlt : firstStop b m' L < firstStop b m L) : firstDecision b m' L = 1 := by
  obtain ⟨hK, hin⟩ := firstStop_min b m L _ hlt
  have hcross := (firstStop_spec b m' L).resolve_left (by omega)
  have hpos : 1/2 < m' (firstStop b m' L) := by
    by_contra hc
    have hc' : m' (firstStop b m' L) ≤ 1/2 := not_lt.mp hc
    rw [abs_of_nonpos (by linarith)] at hcross
    have h3 : 1/2 - m (firstStop b m' L) ≤ |m (firstStop b m' L) - 1/2| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    linarith [h (firstStop b m' L)]
  unfold firstDecision
  simp only [hpos, ite_true]

/-- Raising the means keeps a positive decision positive. -/
theorem firstDecision_one_of_le (b : ℕ → ℕ → ℝ) {m m' : ℕ → ℝ} (h : ∀ k, m k ≤ m' k)
    (L : ℕ) (hd : firstDecision b m L = 1) : firstDecision b m' L = 1 := by
  rcases (firstStop_le_of_decision_one b h L hd).lt_or_eq with hlt | heq
  · exact firstDecision_one_of_stop_lt b h L hlt
  · have hm := half_lt_of_firstDecision_one b m L hd
    have hpos : 1/2 < m' (firstStop b m' L) := by
      rw [heq]
      exact lt_of_lt_of_le hm (h _)
    unfold firstDecision
    simp only [hpos, ite_true]

/-- The running means are monotone in the flips. -/
theorem dyadicMean_mono (k : ℕ) {ω ω' : ℕ → Bool} (h : ω ≤ ω') :
    dyadicMean Tier2.observations k ω ≤ dyadicMean Tier2.observations k ω' := by
  unfold dyadicMean prefixMean
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun i _ => bit_mono (h i)) (by positivity)

/-- More heads do not delay a positive decision of the ordinary classifier. -/
theorem classifierStop_le_of_value_one (L : ℕ) {ω ω' : ℕ → Bool} (h : ω ≤ ω')
    (hv : classifierValue L ω = 1) : classifierStop L ω' ≤ classifierStop L ω :=
  Nat.pow_le_pow_right (by norm_num)
    (firstStop_le_of_decision_one _ (fun k => dyadicMean_mono k h) L hv)

/-- With more heads, a strictly earlier stop of the ordinary classifier is a
positive decision. -/
theorem classifierValue_one_of_stop_lt (L : ℕ) {ω ω' : ℕ → Bool} (h : ω ≤ ω')
    (hlt : classifierStop L ω' < classifierStop L ω) : classifierValue L ω' = 1 :=
  firstDecision_one_of_stop_lt _ (fun k => dyadicMean_mono k h) L
    ((Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt)

/-- More heads keep a positive decision of the ordinary classifier. -/
theorem classifierValue_one_of_le (L : ℕ) {ω ω' : ℕ → Bool} (h : ω ≤ ω')
    (hv : classifierValue L ω = 1) : classifierValue L ω' = 1 :=
  firstDecision_one_of_le _ (fun k => dyadicMean_mono k h) L hv

/-- The decision of the ordinary classifier is monotone in the flips. -/
theorem classifierValue_mono (L : ℕ) : Monotone (classifierValue L) := by
  intro ω ω' h
  rcases Model.decision_zero_or_one (fun k => dyadicMean Tier2.observations k ω) L with h0 | h1
  · change classifierValue L ω = 0 at h0
    rw [h0]
    rcases Model.decision_zero_or_one (fun k => dyadicMean Tier2.observations k ω') L
      with h' | h'
    · exact le_of_eq h'.symm
    · change classifierValue L ω' = 1 at h'
      rw [h']
      norm_num
  · exact le_of_eq ((h1 : classifierValue L ω = 1).trans (classifierValue_one_of_le L h h1).symm)

end ThresholdHC.RobustContinuation
