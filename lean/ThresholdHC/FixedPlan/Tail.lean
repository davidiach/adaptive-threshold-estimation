import ThresholdHC.FixedPlan.Specification

/-! One-coin facts for the fixed plan: the majority vote of `2k+1` flips has mean
`majorityTail k p` at success rate `p`, the binomial tail is symmetric, and the
closed-form misclassification probability is the actual tape probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ThresholdHC.FixedPlan
open ThresholdHC.Tier6 ThresholdHC.Tier2 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation

theorem wordHeads_eq_sum {n : ℕ} (w : Fin n → Bool) :
    wordHeads w = ∑ i, if w i then 1 else 0 := by
  unfold wordHeads
  exact Finset.card_filter _ _

theorem wordHeads_snoc_eq {n : ℕ} (w : Fin n → Bool) (b : Bool) :
    wordHeads (Fin.snoc w b : Fin (n+1) → Bool) = wordHeads w + (if b then 1 else 0) := by
  simp only [wordHeads_eq_sum, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

/-- Words of length `n` grouped by their number of heads. -/
theorem sum_words_by_heads_real (n : ℕ) (F : ℕ → ℝ) :
    (∑ w : Fin n → Bool, F (wordHeads w)) =
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) * F j := by
  induction n generalizing F with
  | zero => simp [wordHeads]
  | succ n ih =>
    have he := (Fin.snocEquiv (fun _ : Fin (n+1) => Bool)).sum_comp (fun w => F (wordHeads w))
    rw [← he, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Fin.snocEquiv_apply, wordHeads_snoc_eq, ite_true,
      Bool.false_eq_true, ite_false, add_zero]
    rw [ih (fun k => F (k+1)), ih F]
    rw [add_comm]
    exact (Finset.sum_choose_succ_mul (fun i _ => F i) n).symm

theorem measurable_majorityVote (k : ℕ) : Measurable (majorityVote k) :=
  (measurable_of_countable (fun w : Fin (2*k+1) → Bool =>
    if k+1 ≤ wordHeads w then (1 : ℝ) else 0)).comp (measurable_prefix (2*k+1))

theorem majorityVote_binary (k : ℕ) (ω : ℕ → Bool) :
    majorityVote k ω = 0 ∨ majorityVote k ω = 1 := by
  unfold majorityVote
  split_ifs <;> simp

theorem majorityVote_mem (k : ℕ) (ω : ℕ → Bool) : majorityVote k ω ∈ Set.Icc (0 : ℝ) 1 := by
  rcases majorityVote_binary k ω with h | h <;> rw [h] <;> constructor <;> norm_num

theorem integrable_majorityVote (k : ℕ) (P : Measure (ℕ → Bool)) [IsFiniteMeasure P] :
    Integrable (majorityVote k) P :=
  Uniform713.integrable_binary (measurable_majorityVote k) (majorityVote_binary k)

theorem majorityTail_eq_range (k : ℕ) (p : ℝ) :
    majorityTail k p = ∑ j ∈ Finset.range (2*k+2),
      ((2*k+1).choose j : ℝ) * (p^j * (1-p)^(2*k+1-j) * if k+1 ≤ j then 1 else 0) := by
  rw [← Finset.sum_range_add_sum_Ico _ (show k+1 ≤ 2*k+2 by omega)]
  have h0 : ∑ j ∈ Finset.range (k+1),
      ((2*k+1).choose j : ℝ) * (p^j * (1-p)^(2*k+1-j) * if k+1 ≤ j then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' : ¬ k+1 ≤ j := by simp only [Finset.mem_range] at hj; omega
    simp [hj']
  rw [h0, zero_add, majorityTail]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : k+1 ≤ j := (Finset.mem_Ico.mp hj).1
  simp only [hj', ite_true, mul_one]
  ring

/-- The majority vote of `2k+1` flips at success rate `p` has mean `majorityTail k p`. -/
theorem majorityVote_integral (k : ℕ) (p : unitInterval) :
    ∫ ω, majorityVote k ω ∂tapeMeasure p = majorityTail k p := by
  have h := integral_prefix p (M := 2*k+1)
    (fun w : Fin (2*k+1) → Bool => if k+1 ≤ wordHeads w then (1 : ℝ) else 0)
  change ∫ ω, (fun w : Fin (2*k+1) → Bool => if k+1 ≤ wordHeads w then (1 : ℝ) else 0)
    (tapePrefix (2*k+1) ω) ∂tapeMeasure p = _
  rw [h]
  simp_rw [streamProb_heads]
  rw [sum_words_by_heads_real (2*k+1) (fun j => (p : ℝ)^j * (1-(p : ℝ))^(2*k+1-j) *
    if k+1 ≤ j then 1 else 0), majorityTail_eq_range]

/-- The lower tail, reflected. -/
theorem majorityTail_one_sub (k : ℕ) (p : ℝ) :
    majorityTail k (1-p) = ∑ i ∈ Finset.range (k+1),
      ((2*k+1).choose i : ℝ) * p^i * (1-p)^(2*k+1-i) := by
  unfold majorityTail
  apply Finset.sum_nbij' (fun j => 2*k+1-j) (fun i => 2*k+1-i)
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    simp only [Finset.mem_range]
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Ico]
    omega
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    omega
  · intro j hj
    have hj' : j ≤ 2*k+1 := by
      simp only [Finset.mem_Ico] at hj
      omega
    rw [Nat.choose_symm hj', Nat.sub_sub_self hj', sub_sub_cancel]
    ring

/-- The upper and lower majority tails add to one. -/
theorem majorityTail_add_symm (k : ℕ) (p : ℝ) : majorityTail k p + majorityTail k (1-p) = 1 := by
  rw [majorityTail_one_sub, add_comm, majorityTail,
    Finset.sum_range_add_sum_Ico _ (show k+1 ≤ 2*k+2 by omega)]
  have h := add_pow p (1-p) (2*k+1)
  rw [add_sub_cancel, one_pow] at h
  refine Eq.trans ?_ h.symm
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem majorityTail_nonneg (k : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ majorityTail k p := by
  unfold majorityTail
  apply Finset.sum_nonneg
  intro j _
  have : 0 ≤ 1-p := by linarith
  positivity

theorem majorityTail_le_one (k : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : majorityTail k p ≤ 1 := by
  have h := majorityTail_add_symm k p
  have hn := majorityTail_nonneg k (p := 1-p) (by linarith) (by linarith)
  linarith

theorem continuous_majorityTail (k : ℕ) : Continuous (majorityTail k) := by
  unfold majorityTail
  fun_prop

theorem gapParameter_false_val (d : Gap) : (gapParameter false d : ℝ) = 1/2 - (d : ℝ) := by
  simp [gapParameter, sub_eq_add_neg]

theorem gapParameter_true_val (d : Gap) : (gapParameter true d : ℝ) = 1/2 + (d : ℝ) := by
  simp [gapParameter]

theorem majorityMiss_nonneg (k : ℕ) (d : Gap) : 0 ≤ majorityMiss k d :=
  majorityTail_nonneg k (by linarith [d.property.2]) (by linarith [d.property.1])

theorem majorityMiss_le_one (k : ℕ) (d : Gap) : majorityMiss k d ≤ 1 :=
  majorityTail_le_one k (by linarith [d.property.2]) (by linarith [d.property.1])

theorem measurable_majorityMiss (k : ℕ) : Measurable (majorityMiss k) :=
  ((continuous_majorityTail k).comp (continuous_const.sub continuous_subtype_val)).measurable

theorem integrable_majorityMiss (μ : Measure Gap) [IsFiniteMeasure μ] (k : ℕ) :
    Integrable (majorityMiss k) μ :=
  Tier5.integrable_of_abs_bound μ _ (measurable_majorityMiss k) 1 (fun d => by
    rw [abs_of_nonneg (majorityMiss_nonneg k d)]
    exact majorityMiss_le_one k d)

/-- Mean vote of a coin with negative sign. -/
theorem majorityVote_integral_false (k : ℕ) (d : Gap) :
    ∫ ω, majorityVote k ω ∂tapeMeasure (gapParameter false d) = majorityMiss k d := by
  rw [majorityVote_integral, gapParameter_false_val]
  rfl

/-- Mean vote of a coin with positive sign. -/
theorem majorityVote_integral_true (k : ℕ) (d : Gap) :
    ∫ ω, majorityVote k ω ∂tapeMeasure (gapParameter true d) = 1 - majorityMiss k d := by
  rw [majorityVote_integral, gapParameter_true_val]
  have h := majorityTail_add_symm k (1/2 + (d : ℝ))
  rw [show (1 : ℝ) - (1/2 + (d : ℝ)) = 1/2 - (d : ℝ) by ring] at h
  unfold majorityMiss
  linarith

/-- The closed form `majorityMiss k d` is the probability of a wrong majority vote,
for either sign. -/
theorem majorityVote_error (k : ℕ) (d : Gap) (s : Bool) :
    (tapeMeasure (gapParameter s d)).real {ω | majorityVote k ω ≠ bit s} = majorityMiss k d := by
  rw [← Uniform713.integral_binary_error (measurable_majorityVote k) measurable_const
    (majorityVote_binary k) (fun _ => by cases s <;> simp [bit])]
  have hi := integrable_majorityVote k (tapeMeasure (gapParameter s d))
  cases s
  · have he : (fun ω => |majorityVote k ω - bit false|) = majorityVote k := by
      funext ω
      rcases majorityVote_binary k ω with h | h <;> simp [h, bit]
    rw [he, majorityVote_integral_false]
  · have he : (fun ω => |majorityVote k ω - bit true|) = fun ω => 1 - majorityVote k ω := by
      funext ω
      rcases majorityVote_binary k ω with h | h <;> simp [h, bit]
    rw [he, integral_sub (integrable_const 1) hi, majorityVote_integral_true]
    simp

end ThresholdHC.FixedPlan
