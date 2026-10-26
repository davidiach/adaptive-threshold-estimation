import ThresholdHC.Uniform713.Common

open MeasureTheory
namespace ThresholdHC.Uniform713

noncomputable def firstStop (b : ℕ → ℕ → ℝ) (m : ℕ → ℝ) (L : ℕ) : ℕ :=
  by classical exact Nat.find (show ∃ k, L ≤ k ∨ b k L < |m k - 1/2| from
    ⟨L, Or.inl le_rfl⟩)

theorem firstStop_le (b : ℕ → ℕ → ℝ) (m : ℕ → ℝ) (L : ℕ) :
    firstStop b m L ≤ L := by
  classical
  exact Nat.find_min' _ (Or.inl le_rfl)

theorem firstStop_spec (b : ℕ → ℕ → ℝ) (m : ℕ → ℝ) (L : ℕ) :
    L ≤ firstStop b m L ∨ b (firstStop b m L) L < |m (firstStop b m L) - 1/2| := by
  classical
  exact Nat.find_spec (show ∃ k, L ≤ k ∨ b k L < |m k - 1/2| from
    ⟨L, Or.inl le_rfl⟩)

theorem firstStop_min (b : ℕ → ℕ → ℝ) (m : ℕ → ℝ) (L k : ℕ)
    (hk : k < firstStop b m L) :
    k < L ∧ |m k - 1/2| ≤ b k L := by
  classical
  have h := Nat.find_min (show ∃ k, L ≤ k ∨ b k L < |m k - 1/2| from
    ⟨L, Or.inl le_rfl⟩) hk
  simpa only [not_or, not_le, not_lt] using h

theorem firstStop_le_of_cross (b : ℕ → ℕ → ℝ) (m : ℕ → ℝ) (L k : ℕ)
    (hk : b k L < |m k - 1/2|) : firstStop b m L ≤ k := by
  classical
  exact Nat.find_min' _ (Or.inr hk)

theorem firstStop_mono (b : ℕ → ℕ → ℝ) (m : ℕ → ℝ) {L K : ℕ}
    (hLK : L ≤ K) (hb : ∀ k < L, b k L ≤ b k K) :
    firstStop b m L ≤ firstStop b m K := by
  by_cases hs : L ≤ firstStop b m K
  · exact (firstStop_le b m L).trans hs
  · have hsL : firstStop b m K < L := lt_of_not_ge hs
    have hcross := (firstStop_spec b m K).resolve_left (by omega)
    exact firstStop_le_of_cross _ _ _ _ ((hb _ hsL).trans_lt hcross)

theorem firstStop_eq_iff (b : ℕ → ℕ → ℝ) (m : ℕ → ℝ) (L k : ℕ) :
    firstStop b m L = k ↔
      (L ≤ k ∨ b k L < |m k - 1/2|) ∧
        ∀ j < k, j < L ∧ |m j - 1/2| ≤ b j L := by
  classical
  rw [firstStop, Nat.find_eq_iff]
  simp only [not_or, not_le, not_lt]

theorem measurable_firstStop {Ω : Type*} [MeasurableSpace Ω]
    (b : ℕ → ℕ → ℝ) (m : ℕ → Ω → ℝ)
    (hm : ∀ k, Measurable (m k)) (L : ℕ) :
    Measurable (fun ω => firstStop b (fun k => m k ω) L) := by
  apply measurable_to_countable'
  intro k
  have heq : {ω | firstStop b (fun j => m j ω) L = k} =
      ({ω | L ≤ k} ∪ {ω | b k L < |m k ω - 1/2|}) ∩
        ⋂ j, ⋂ (_ : j < k), ({ω | j < L} ∩ {ω | |m j ω - 1/2| ≤ b j L}) := by
    ext ω
    simp [firstStop_eq_iff]
  change MeasurableSet {ω | firstStop b (fun j => m j ω) L = k}
  rw [heq]
  apply MeasurableSet.inter
  · exact (MeasurableSet.const _).union (measurableSet_lt measurable_const
      ((hm k).sub_const _).abs)
  · exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      (MeasurableSet.const _).inter (measurableSet_le ((hm j).sub_const _).abs measurable_const)

noncomputable def firstDecision (b : ℕ → ℕ → ℝ) (m : ℕ → ℝ) (L : ℕ) : ℝ :=
  if 1/2 < m (firstStop b m L) then 1 else 0

theorem firstDecision_zero_or_one (b : ℕ → ℕ → ℝ) (m : ℕ → ℝ) (L : ℕ) :
    firstDecision b m L = 0 ∨ firstDecision b m L = 1 := by
  unfold firstDecision
  split_ifs <;> simp

theorem wrong_positive_stop (b : ℕ → ℕ → ℝ) (m : ℕ → ℝ) (L : ℕ)
    (d : ℝ) (hwrong : firstDecision b m L ≠ 1) :
    (firstStop b m L = L ∧ d ≤ (1/2+d)-m L) ∨
      (firstStop b m L < L ∧
        d+b (firstStop b m L) L ≤ (1/2+d)-m (firstStop b m L)) := by
  have hm : m (firstStop b m L) ≤ 1/2 := by
    simpa [firstDecision] using hwrong
  by_cases hs : firstStop b m L = L
  · left; constructor
    · exact hs
    · rw [hs] at hm; linarith
  · have hlt := lt_of_le_of_ne (firstStop_le _ _ _) hs
    right; refine ⟨hlt, ?_⟩
    have hc := (firstStop_spec b m L).resolve_left (by omega)
    rw [abs_of_nonpos (by linarith : m (firstStop b m L)-1/2 ≤ 0)] at hc
    linarith

theorem wrong_negative_stop (b : ℕ → ℕ → ℝ) (m : ℕ → ℝ) (L : ℕ)
    (d : ℝ) (hwrong : firstDecision b m L ≠ 0) :
    (firstStop b m L = L ∧ d ≤ m L-(1/2-d)) ∨
      (firstStop b m L < L ∧
        d+b (firstStop b m L) L ≤ m (firstStop b m L)-(1/2-d)) := by
  have hm : 1/2 < m (firstStop b m L) := by
    simpa [firstDecision] using hwrong
  by_cases hs : firstStop b m L = L
  · left; constructor
    · exact hs
    · rw [hs] at hm; linarith
  · have hlt := lt_of_le_of_ne (firstStop_le _ _ _) hs
    right; refine ⟨hlt, ?_⟩
    have hc := (firstStop_spec b m L).resolve_left (by omega)
    rw [abs_of_nonneg (by linarith : 0 ≤ m (firstStop b m L)-1/2)] at hc
    linarith

theorem dyadic_survival_identity (s L : ℕ) (hs : s ≤ L) :
    (2:ℝ)^s = 1 + ∑ k ∈ Finset.range L, if k < s then (2:ℝ)^k else 0 := by
  induction L generalizing s with
  | zero =>
    have : s = 0 := by omega
    simp [this]
  | succ L ih =>
    rw [Finset.sum_range_succ]
    by_cases hsL : s ≤ L
    · rw [if_neg (by omega)]
      simpa using ih s hsL
    · have hsEq : s = L+1 := by omega
      subst s
      have hsum : (∑ k ∈ Finset.range L, if k < L+1 then (2:ℝ)^k else 0) =
          ∑ k ∈ Finset.range L, if k < L then (2:ℝ)^k else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkL := Finset.mem_range.mp hk
        simp [hkL, show k < L+1 by omega]
      rw [hsum, if_pos (by omega), pow_succ]
      have := ih L (show L ≤ L by rfl)
      linarith

noncomputable def stopLevel (m : ℕ → ℝ) (L : ℕ) : ℕ :=
  firstStop (fun k L => threshold (cap k) (cap L)) m L

noncomputable def decision (m : ℕ → ℝ) (L : ℕ) : ℝ :=
  firstDecision (fun k L => threshold (cap k) (cap L)) m L

noncomputable def work (m : ℕ → ℝ) (L : ℕ) : ℝ := cap (stopLevel m L)

theorem stopLevel_le (m : ℕ → ℝ) (L : ℕ) : stopLevel m L ≤ L :=
  firstStop_le _ _ _

theorem cap_mono {k L : ℕ} (hk : k ≤ L) : cap k ≤ cap L := by
  exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk

theorem threshold_nonneg (n N : ℝ) : 0 ≤ threshold n N := Real.sqrt_nonneg _

theorem threshold_sq {n N : ℝ} (hn : 0 < n) (hnN : n ≤ N) :
    (threshold n N)^2 = (1/4 + Real.log (N/n))/n := by
  apply Real.sq_sqrt
  have : 0 ≤ Real.log (N/n) := Real.log_nonneg ((one_le_div hn).2 hnN)
  positivity

theorem threshold_mono_cap (k : ℕ) {L K : ℕ} (hLK : L ≤ K) :
    threshold (cap k) (cap L) ≤ threshold (cap k) (cap K) := by
  unfold threshold
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (cap_pos k).le
  apply add_le_add_right
  exact Real.log_le_log (div_pos (cap_pos L) (cap_pos k))
    (div_le_div_of_nonneg_right (cap_mono hLK) (cap_pos k).le)

theorem stopLevel_mono (m : ℕ → ℝ) {L K : ℕ} (hLK : L ≤ K) :
    stopLevel m L ≤ stopLevel m K :=
  firstStop_mono _ _ hLK (fun k _ => threshold_mono_cap k hLK)

theorem work_pos (m : ℕ → ℝ) (L : ℕ) : 0 < work m L := cap_pos _

theorem work_le_cap (m : ℕ → ℝ) (L : ℕ) : work m L ≤ cap L :=
  cap_mono (stopLevel_le m L)

theorem work_mono (m : ℕ → ℝ) {L K : ℕ} (hLK : L ≤ K) :
    work m L ≤ work m K := cap_mono (stopLevel_mono m hLK)

theorem coupled_work_eq (m : ℕ → ℝ) (L : ℕ) :
    max (work m L) (work m (L+1)) = work m (L+1) :=
  max_eq_right (work_mono m (Nat.le_succ L))

theorem decision_zero_or_one (m : ℕ → ℝ) (L : ℕ) :
    decision m L = 0 ∨ decision m L = 1 := firstDecision_zero_or_one _ _ _

section Measure
variable {Ω : Type*} [MeasurableSpace Ω] (m : ℕ → Ω → ℝ)
  (hm : ∀ k, Measurable (m k))
include hm

theorem measurable_stopLevel (L : ℕ) :
    Measurable (fun ω => stopLevel (fun k => m k ω) L) :=
  measurable_firstStop _ _ hm _

theorem measurable_decision (L : ℕ) :
    Measurable (fun ω => decision (fun k => m k ω) L) := by
  have hmean : Measurable (fun ω => m (stopLevel (fun k => m k ω) L) ω) :=
    (measurable_from_prod_countable_left (f := fun p : Ω × ℕ => m p.2 p.1)
      (fun k => hm k)).comp
      (measurable_id.prodMk (measurable_stopLevel m hm L))
  exact Measurable.ite (measurableSet_lt measurable_const hmean)
    measurable_const measurable_const

theorem measurable_work (L : ℕ) :
    Measurable (fun ω => work (fun k => m k ω) L) :=
  (measurable_of_countable cap).comp (measurable_stopLevel m hm L)

theorem integrable_work (μ : Measure Ω) [IsFiniteMeasure μ] (L : ℕ) :
    Integrable (fun ω => work (fun k => m k ω) L) μ := by
  apply (integrable_const (cap L)).mono' (measurable_work m hm L).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_pos (work_pos _ _)]
    exact work_le_cap _ _

theorem integrable_decision (μ : Measure Ω) [IsFiniteMeasure μ] (L : ℕ) :
    Integrable (fun ω => decision (fun k => m k ω) L) μ := by
  apply (integrable_const (1:ℝ)).mono' (measurable_decision m hm L).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rcases decision_zero_or_one (fun k => m k ω) L with h | h <;> simp [h]

omit hm in
theorem work_survival_identity (L : ℕ) (ω : Ω) :
    work (fun k => m k ω) L =
      1 + ∑ k ∈ Finset.range L, if k < stopLevel (fun j => m j ω) L then cap k else 0 :=
  dyadic_survival_identity _ _ (stopLevel_le _ _)

theorem expected_work_survival_identity (μ : Measure Ω) [IsProbabilityMeasure μ] (L : ℕ) :
    (∫ ω, work (fun k => m k ω) L ∂μ) =
      1 + ∑ k ∈ Finset.range L, cap k * μ.real {ω | k < stopLevel (fun j => m j ω) L} := by
  classical
  let f : ℕ → Ω → ℝ := fun k =>
    {ω | k < stopLevel (fun j => m j ω) L}.indicator (fun _ => cap k)
  have hs (k : ℕ) : MeasurableSet {ω | k < stopLevel (fun j => m j ω) L} :=
    measurableSet_lt measurable_const (measurable_stopLevel m hm L)
  have hf (k : ℕ) : Integrable (f k) μ := (integrable_const _).indicator (hs k)
  have heq : (fun ω => work (fun k => m k ω) L) =
      fun ω => 1 + ∑ k ∈ Finset.range L, f k ω := by
    funext ω
    rw [work_survival_identity m L ω]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : k < stopLevel (fun j => m j ω) L <;> simp [f, h]
  rw [heq, integral_add (integrable_const _) (integrable_finsetSum _ (fun k _ => hf k)),
    integral_finsetSum _ (fun k _ => hf k)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simpa [f, mul_comm] using integral_indicator_const (cap k) (hs k)

end Measure
end ThresholdHC.Uniform713

