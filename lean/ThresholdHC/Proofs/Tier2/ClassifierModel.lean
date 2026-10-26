import ThresholdHC.Statements2
import ThresholdHC.Uniform713.ClassifierModel
import ThresholdHC.Proofs.Classifier
noncomputable section
namespace ThresholdHC.Tier2.Model
open MeasureTheory Real Uniform713

def threshold1 (n N : ℝ) : ℝ := Real.sqrt ((1 + Real.log (N/n))/n)
def errorPrefactor : ℝ := (5/3)*Real.exp (-2)
theorem errorPrefactor_le : errorPrefactor ≤ 3/5 := by
  have he : 5 ≤ Real.exp (2:ℝ) := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 2)
    norm_num at h
    linarith
  have hi : Real.exp (-2) ≤ (1/5:ℝ) := by
    rw [Real.exp_neg]
    apply (inv_le_iff_one_le_mul₀ (Real.exp_pos (2:ℝ))).2
    linarith
  unfold errorPrefactor
  linarith
noncomputable def stopLevel (m : ℕ → ℝ) (L : ℕ) : ℕ :=
  firstStop (fun k L => threshold1 (cap k) (cap L)) m L

noncomputable def decision (m : ℕ → ℝ) (L : ℕ) : ℝ :=
  firstDecision (fun k L => threshold1 (cap k) (cap L)) m L

noncomputable def work (m : ℕ → ℝ) (L : ℕ) : ℝ := cap (stopLevel m L)

theorem stopLevel_le (m : ℕ → ℝ) (L : ℕ) : stopLevel m L ≤ L :=
  firstStop_le _ _ _

theorem cap_mono {k L : ℕ} (hk : k ≤ L) : cap k ≤ cap L := by
  exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk

theorem threshold1_nonneg (n N : ℝ) : 0 ≤ threshold1 n N := Real.sqrt_nonneg _

theorem threshold1_sq {n N : ℝ} (hn : 0 < n) (hnN : n ≤ N) :
    (threshold1 n N)^2 = (1 + Real.log (N/n))/n := by
  apply Real.sq_sqrt
  have : 0 ≤ Real.log (N/n) := Real.log_nonneg ((one_le_div hn).2 hnN)
  positivity

theorem threshold1_mono_cap (k : ℕ) {L K : ℕ} (hLK : L ≤ K) :
    threshold1 (cap k) (cap L) ≤ threshold1 (cap k) (cap K) := by
  unfold threshold1
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (cap_pos k).le
  apply add_le_add_right
  exact Real.log_le_log (div_pos (cap_pos L) (cap_pos k))
    (div_le_div_of_nonneg_right (cap_mono hLK) (cap_pos k).le)

theorem stopLevel_mono (m : ℕ → ℝ) {L K : ℕ} (hLK : L ≤ K) :
    stopLevel m L ≤ stopLevel m K :=
  firstStop_mono _ _ hLK (fun k _ => threshold1_mono_cap k hLK)

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


theorem survival_indicator_scale_step (n N d : ℝ) (hn : 0 < n) (hnN : n ≤ N)
    (hd : 0 < d) (hNd : 1 ≤ N*d^2) (hstop : d ≤ 2*threshold1 n N) :
    n*d^2 ≤ 4*(1+Real.log (N*d^2)) := by
  exact ThresholdHC.Proofs.classifier_scale_step n N d hn hnN hd hNd hstop

theorem finite_work_survival_bound (L : ℕ) (d : ℝ) (hd : 0 < d)
    (hdmax : d ≤ 1/2) (hscale : 1 ≤ cap L*d^2) :
    1 + (∑ k ∈ Finset.range L, cap k *
      ((if d ≤ (2:ℝ)*threshold1 (cap k) (cap L) then 1 else 0) +
        Real.exp (-(2*(1/2:ℝ)^2*d^2*cap k)))) ≤
      17*(d⁻¹)^2*(1+Real.log (cap L*d^2)) := by
  classical
  let A := 4*(1+Real.log (cap L*d^2))
  have hlog : 0 ≤ Real.log (cap L*d^2) := Real.log_nonneg hscale
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hI : (∑ k ∈ Finset.range L, cap k *
      (if d ≤ (2:ℝ)*threshold1 (cap k) (cap L) then 1 else 0)) ≤
        2*A/d^2 := by
    calc
      _ ≤ ∑ k ∈ Finset.range L, if cap k*d^2 ≤ A then cap k else 0 := by
        apply Finset.sum_le_sum
        intro k hk
        have hkL : cap k ≤ cap L := cap_mono (Finset.mem_range.mp hk).le
        split_ifs with h h' h'
        · simp
        · have := survival_indicator_scale_step (cap k) (cap L) d (cap_pos k) hkL hd hscale h
          exact (h' this).elim
        · simpa using (cap_pos k).le
        · simp
      _ ≤ _ := finite_dyadic_scaled_indicator_sum L d A hd hA
  have hb : 0 < 2*(1/2:ℝ)^2*d^2 := by positivity
  have hE := finite_dyadic_sum_v1 (2*(1/2:ℝ)^2*d^2) hb L
  have hsum : 1 + (∑ k ∈ Finset.range L, cap k *
      ((if d ≤ (2:ℝ)*threshold1 (cap k) (cap L) then 1 else 0) +
        Real.exp (-(2*(1/2:ℝ)^2*d^2*cap k)))) ≤
      1+2*A/d^2+2/(2*(1/2:ℝ)^2*d^2) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    linarith
  apply le_trans hsum
  have hd2 : 0 < d^2 := sq_pos_of_pos hd
  have hdone : (1:ℝ) ≤ (1/4)/d^2 := by
    apply (le_div_iff₀ hd2).2
    nlinarith
  have hcoeff : (49/4:ℝ)+8*Real.log (cap L*d^2) ≤
      17*(1+Real.log (cap L*d^2)) := by nlinarith
  calc
    _ ≤ (1/4)/d^2+2*A/d^2+2/(2*(1/2:ℝ)^2*d^2) := by linarith
    _ = ((49/4:ℝ)+8*Real.log (cap L*d^2))/d^2 := by
      dsimp [A]
      field_simp
      <;> ring
    _ ≤ (17*(1+Real.log (cap L*d^2)))/d^2 :=
      div_le_div_of_nonneg_right hcoeff hd2.le
    _ = _ := by field_simp

def errorUnionBound (L : ℕ) (d : ℝ) : ℝ :=
  Real.exp (-2 * cap L * d^2) +
    ∑ k ∈ Finset.range L,
      Real.exp (-2 * cap k * (d + threshold1 (cap k) (cap L))^2)

section Probability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {m : ℕ → Ω → ℝ}

theorem error_positive_union (L : ℕ) {d : ℝ} (hd : 0 < d)
    (ht : HasMeanTails μ m (1/2+d)) :
    μ.real {ω | decision (fun k => m k ω) L ≠ 1} ≤ errorUnionBound L d := by
  have hsub : {ω | decision (fun k => m k ω) L ≠ 1} ⊆
      {ω | d ≤ (1/2+d)-m L ω} ∪
        ⋃ k ∈ Finset.range L,
          {ω | d+threshold1 (cap k) (cap L) ≤ (1/2+d)-m k ω} := by
    intro ω hω
    rcases wrong_positive_stop (fun k L => threshold1 (cap k) (cap L))
      (fun k => m k ω) L d hω with ⟨hs,h⟩ | ⟨hs,h⟩
    · exact Or.inl h
    · right
      exact Set.mem_iUnion.2 ⟨_, Set.mem_iUnion.2 ⟨Finset.mem_range.2 hs,h⟩⟩
  calc
    _ ≤ μ.real ({ω | d ≤ (1/2+d)-m L ω} ∪
        ⋃ k ∈ Finset.range L,
          {ω | d+threshold1 (cap k) (cap L) ≤ (1/2+d)-m k ω}) := measureReal_mono hsub
    _ ≤ μ.real {ω | d ≤ (1/2+d)-m L ω} +
        ∑ k ∈ Finset.range L,
          μ.real {ω | d+threshold1 (cap k) (cap L) ≤ (1/2+d)-m k ω} :=
      (measureReal_union_le _ _).trans
        (add_le_add_right (measureReal_biUnion_finset_le _ _) _)
    _ ≤ errorUnionBound L d := by
      unfold errorUnionBound
      apply add_le_add (ht.lower L d hd.le)
      apply Finset.sum_le_sum
      intro k hk
      exact ht.lower k _ (add_nonneg hd.le (threshold1_nonneg _ _))

theorem error_negative_union (L : ℕ) {d : ℝ} (hd : 0 < d)
    (ht : HasMeanTails μ m (1/2-d)) :
    μ.real {ω | decision (fun k => m k ω) L ≠ 0} ≤ errorUnionBound L d := by
  have hsub : {ω | decision (fun k => m k ω) L ≠ 0} ⊆
      {ω | d ≤ m L ω-(1/2-d)} ∪
        ⋃ k ∈ Finset.range L,
          {ω | d+threshold1 (cap k) (cap L) ≤ m k ω-(1/2-d)} := by
    intro ω hω
    rcases wrong_negative_stop (fun k L => threshold1 (cap k) (cap L))
      (fun k => m k ω) L d hω with ⟨hs,h⟩ | ⟨hs,h⟩
    · exact Or.inl h
    · right
      exact Set.mem_iUnion.2 ⟨_, Set.mem_iUnion.2 ⟨Finset.mem_range.2 hs,h⟩⟩
  calc
    _ ≤ μ.real ({ω | d ≤ m L ω-(1/2-d)} ∪
        ⋃ k ∈ Finset.range L,
          {ω | d+threshold1 (cap k) (cap L) ≤ m k ω-(1/2-d)}) := measureReal_mono hsub
    _ ≤ μ.real {ω | d ≤ m L ω-(1/2-d)} +
        ∑ k ∈ Finset.range L,
          μ.real {ω | d+threshold1 (cap k) (cap L) ≤ m k ω-(1/2-d)} :=
      (measureReal_union_le _ _).trans
        (add_le_add_right (measureReal_biUnion_finset_le _ _) _)
    _ ≤ errorUnionBound L d := by
      unfold errorUnionBound
      apply add_le_add (ht.upper L d hd.le)
      apply Finset.sum_le_sum
      intro k hk
      exact ht.upper k _ (add_nonneg hd.le (threshold1_nonneg _ _))

theorem error_le_one (L : ℕ) (s : ℝ) :
    μ.real {ω | decision (fun k => m k ω) L ≠ s} ≤ 1 := measureReal_le_one

theorem survival_probability_positive (L k : ℕ) {d : ℝ} (hd : 0 < d)
    (ht : HasMeanTails μ m (1/2+d)) :
    μ.real {ω | k < stopLevel (fun j => m j ω) L} ≤
      (if d ≤ (2:ℝ)*threshold1 (cap k) (cap L) then 1 else 0) +
        Real.exp (-(2*(1/2:ℝ)^2*d^2*cap k)) := by
  split_ifs with h
  · have hp : μ.real {ω | k < stopLevel (fun j => m j ω) L} ≤ 1 := measureReal_le_one
    linarith [Real.exp_pos (-(2*(1/2:ℝ)^2*d^2*cap k))]
  · have hsub : {ω | k < stopLevel (fun j => m j ω) L} ⊆
        {ω | (1/2:ℝ)*d ≤ (1/2+d)-m k ω} := by
      intro ω hω
      have hs := (firstStop_min (fun k L => threshold1 (cap k) (cap L))
        (fun j => m j ω) L k hω).2
      have hu := (abs_le.mp hs).2
      simp only [Set.mem_ofPred_eq]
      linarith
    have hp := (measureReal_mono hsub).trans (ht.lower k ((1/2:ℝ)*d) (by positivity))
    have heq : -2*cap k*((1/2:ℝ)*d)^2 = -(2*(1/2:ℝ)^2*d^2*cap k) := by ring
    rw [heq] at hp
    simpa only [zero_add] using hp

theorem survival_probability_negative (L k : ℕ) {d : ℝ} (hd : 0 < d)
    (ht : HasMeanTails μ m (1/2-d)) :
    μ.real {ω | k < stopLevel (fun j => m j ω) L} ≤
      (if d ≤ (2:ℝ)*threshold1 (cap k) (cap L) then 1 else 0) +
        Real.exp (-(2*(1/2:ℝ)^2*d^2*cap k)) := by
  split_ifs with h
  · have hp : μ.real {ω | k < stopLevel (fun j => m j ω) L} ≤ 1 := measureReal_le_one
    linarith [Real.exp_pos (-(2*(1/2:ℝ)^2*d^2*cap k))]
  · have hsub : {ω | k < stopLevel (fun j => m j ω) L} ⊆
        {ω | (1/2:ℝ)*d ≤ m k ω-(1/2-d)} := by
      intro ω hω
      have hs := (firstStop_min (fun k L => threshold1 (cap k) (cap L))
        (fun j => m j ω) L k hω).2
      have hl := (abs_le.mp hs).1
      simp only [Set.mem_ofPred_eq]
      linarith
    have hp := (measureReal_mono hsub).trans (ht.upper k ((1/2:ℝ)*d) (by positivity))
    have heq : -2*cap k*((1/2:ℝ)*d)^2 = -(2*(1/2:ℝ)^2*d^2*cap k) := by ring
    rw [heq] at hp
    simpa only [zero_add] using hp

theorem expected_work_le_cap (hm : ∀ k, Measurable (m k)) (L : ℕ) :
    (∫ ω, work (fun k => m k ω) L ∂μ) ≤ cap L := by
  calc
    _ ≤ ∫ _ : Ω, cap L ∂μ :=
      integral_mono (integrable_work m hm μ L) (integrable_const _)
        (fun ω => work_le_cap _ _)
    _ = _ := by simp

theorem expected_work_survival_bound (L : ℕ) {d : ℝ}
    (hm : ∀ k, Measurable (m k))
    (hs : ∀ k, μ.real {ω | k < stopLevel (fun j => m j ω) L} ≤
      (if d ≤ (2:ℝ)*threshold1 (cap k) (cap L) then 1 else 0) +
        Real.exp (-(2*(1/2:ℝ)^2*d^2*cap k))) :
    (∫ ω, work (fun k => m k ω) L ∂μ) ≤
      1 + ∑ k ∈ Finset.range L, cap k *
        ((if d ≤ (2:ℝ)*threshold1 (cap k) (cap L) then 1 else 0) +
          Real.exp (-(2*(1/2:ℝ)^2*d^2*cap k))) := by
  rw [expected_work_survival_identity m hm μ L]
  apply add_le_add_right
  exact Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hs k) (cap_pos k).le)

theorem squared_decision_difference_integral (hm : ∀ k, Measurable (m k)) (K L : ℕ) :
    (∫ ω, (decision (fun k => m k ω) K-decision (fun k => m k ω) L)^2 ∂μ) =
      μ.real {ω | decision (fun k => m k ω) K ≠ decision (fun k => m k ω) L} := by
  classical
  have heq : (fun ω => (decision (fun k => m k ω) K-decision (fun k => m k ω) L)^2) =
      {ω | decision (fun k => m k ω) K ≠ decision (fun k => m k ω) L}.indicator
        (fun _ => (1:ℝ)) := by
    funext ω
    rcases decision_zero_or_one (fun k => m k ω) K with hK | hK <;>
      rcases decision_zero_or_one (fun k => m k ω) L with hL | hL <;>
      simp [hK,hL,Set.indicator]
  have hset : MeasurableSet
      {ω | decision (fun k => m k ω) K ≠ decision (fun k => m k ω) L} :=
    (measurableSet_eq_fun (measurable_decision m hm K) (measurable_decision m hm L)).compl
  rw [heq, integral_indicator_const (1:ℝ) hset]
  simp

theorem squared_decision_difference_le_errors (hm : ∀ k, Measurable (m k)) (K L : ℕ) (s : ℝ) :
    (∫ ω, (decision (fun k => m k ω) K-decision (fun k => m k ω) L)^2 ∂μ) ≤
      μ.real {ω | decision (fun k => m k ω) K ≠ s} +
        μ.real {ω | decision (fun k => m k ω) L ≠ s} := by
  rw [squared_decision_difference_integral hm K L]
  apply le_trans (measureReal_mono (s₂ :=
      {ω | decision (fun k => m k ω) K ≠ s} ∪
      {ω | decision (fun k => m k ω) L ≠ s}) ?_) (measureReal_union_le _ _)
  intro ω hω
  simp only [Set.mem_union,Set.mem_ofPred_eq] at *
  by_contra h
  push Not at h
  exact hω (h.1.trans h.2.symm)

theorem squared_decision_difference_le_one (hm : ∀ k, Measurable (m k)) (K L : ℕ) :
    (∫ ω, (decision (fun k => m k ω) K-decision (fun k => m k ω) L)^2 ∂μ) ≤ 1 := by
  rw [squared_decision_difference_integral hm K L]
  exact measureReal_le_one

end Probability

theorem early_error_term {n N d : ℝ} (hn : 0 < n) (hnN : n ≤ N) (hd : 0 ≤ d) :
    Real.exp (-2*n*(d+threshold1 n N)^2) ≤
      Real.exp ((-2:ℝ))/N^2 * (n^2*Real.exp (-(2*d^2*n))) := by
  have hN : 0 < N := hn.trans_le hnN
  have ht := threshold1_nonneg n N
  have hs := threshold1_sq hn hnN
  have hexp : -2*n*(d+threshold1 n N)^2 ≤ -2*n*(d^2+(threshold1 n N)^2) := by
    nlinarith [mul_nonneg hd ht, mul_nonneg hn.le (mul_nonneg hd ht)]
  refine (Real.exp_le_exp.2 hexp).trans_eq ?_
  have heq : -2*n*(d^2+(threshold1 n N)^2) =
      -(2*d^2*n) + ((-2:ℝ)) + -(2*Real.log (N/n)) := by
    rw [hs]
    field_simp
    <;> ring
  have he2 : Real.exp (2*Real.log (N/n)) = (N/n)^2 := by
    rw [show 2*Real.log (N/n) = Real.log (N/n)+Real.log (N/n) by ring,
      Real.exp_add, Real.exp_log (div_pos hN hn)]
    ring
  rw [heq, Real.exp_add, Real.exp_add, Real.exp_neg (2*Real.log (N/n)), he2]
  field_simp

theorem exp_cap_error {x : ℝ} (hx : 0 < x) :
    Real.exp (-2*x) ≤ Real.exp (-2)/x^2 := by
  have h : x ≤ Real.exp (x-1) := by linarith [Real.add_one_le_exp (x-1)]
  have hs : x^2 ≤ (Real.exp (x-1))^2 := by nlinarith [Real.exp_pos (x-1)]
  apply (le_div_iff₀ (sq_pos_of_pos hx)).2
  have hp := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-2*x)).le
  have heq : (Real.exp (x-1))^2*Real.exp (-2*x) = Real.exp (-2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hp
  nlinarith only [hp]

theorem errorUnionBound_le (L : ℕ) {d : ℝ} (hd : 0 < d) :
    errorUnionBound L d ≤ errorPrefactor/(cap L*d^2)^2 := by
  have hN := cap_pos L
  have hdne := hd.ne'
  have hNne := hN.ne'
  have hsum : (∑ k ∈ Finset.range L,
      Real.exp (-2*cap k*(d+threshold1 (cap k) (cap L))^2)) ≤
      Real.exp ((-2:ℝ))/(cap L)^2 * (8/(3*(2*d^2)^2)) := by
    calc
      _ ≤ ∑ k ∈ Finset.range L,
          Real.exp ((-2:ℝ))/(cap L)^2 * ((cap k)^2*Real.exp (-(2*d^2*cap k))) := by
        apply Finset.sum_le_sum
        intro k hk
        exact early_error_term (cap_pos k) (cap_mono (Finset.mem_range.mp hk).le) hd.le
      _ = Real.exp ((-2:ℝ))/(cap L)^2 *
          ∑ k ∈ Finset.range L, (cap k)^2*Real.exp (-(2*d^2*cap k)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (finite_dyadic_sum_v2 (by positivity) L)
        (by positivity)
  have he := exp_cap_error (show 0 < cap L*d^2 by positivity)
  unfold errorUnionBound errorPrefactor
  have heq : Real.exp (-2*(cap L*d^2)) = Real.exp (-2*cap L*d^2) := by congr 1; ring
  rw [heq] at he
  calc
    _ ≤ Real.exp (-2)/(cap L*d^2)^2 +
        Real.exp ((-2:ℝ))/(cap L)^2 * (8/(3*(2*d^2)^2)) := add_le_add he hsum
    _ = _ := by field_simp; ring

theorem error_positive_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : ℕ → Ω → ℝ} (L : ℕ) {d : ℝ} (hd : 0 < d)
    (ht : HasMeanTails μ m (1/2+d)) :
    μ.real {ω | decision (fun k => m k ω) L ≠ 1} ≤ errorPrefactor/(cap L*d^2)^2 :=
  (error_positive_union L hd ht).trans (errorUnionBound_le L hd)

theorem error_negative_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : ℕ → Ω → ℝ} (L : ℕ) {d : ℝ} (hd : 0 < d)
    (ht : HasMeanTails μ m (1/2-d)) :
    μ.real {ω | decision (fun k => m k ω) L ≠ 0} ≤ errorPrefactor/(cap L*d^2)^2 :=
  (error_negative_union L hd ht).trans (errorUnionBound_le L hd)

section FinalBounds
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {m : ℕ → Ω → ℝ}

theorem measurable_classifier_increment (hm : ∀ k, Measurable (m k)) (L : ℕ) :
    Measurable (fun ω => increment (fun k => decision (fun j => m j ω) k) L) := by
  cases L with
  | zero => exact measurable_decision m hm 0
  | succ L => exact (measurable_decision m hm (L+1)).sub (measurable_decision m hm L)

theorem integrable_classifier_increment (hm : ∀ k, Measurable (m k)) (L : ℕ) :
    Integrable (fun ω => increment (fun k => decision (fun j => m j ω) k) L) μ := by
  cases L with
  | zero => exact integrable_decision m hm μ 0
  | succ L => exact (integrable_decision m hm μ (L+1)).sub (integrable_decision m hm μ L)

theorem classifier_increment_sq_le_one (m : ℕ → ℝ) (L : ℕ) :
    (increment (decision m) L)^2 ≤ 1 := by
  cases L with
  | zero =>
    rcases decision_zero_or_one m 0 with h | h <;> simp [increment,h]
  | succ L =>
    rcases decision_zero_or_one m (L+1) with hK | hK <;>
      rcases decision_zero_or_one m L with hL | hL <;> simp [increment,hK,hL]

theorem integrable_classifier_increment_sq (hm : ∀ k, Measurable (m k)) (L : ℕ) :
    Integrable (fun ω => (increment (fun k => decision (fun j => m j ω) k) L)^2) μ := by
  apply (integrable_const (1:ℝ)).mono'
    ((measurable_classifier_increment hm L).pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact classifier_increment_sq_le_one (fun j => m j ω) L

theorem work_bound_of_survival (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1/2)
    (hm : ∀ k, Measurable (m k))
    (hs : ∀ k, μ.real {ω | k < stopLevel (fun j => m j ω) L} ≤
      (if d ≤ (2:ℝ)*threshold1 (cap k) (cap L) then 1 else 0) +
        Real.exp (-(2*(1/2:ℝ)^2*d^2*cap k))) :
    (∫ ω, work (fun k => m k ω) L ∂μ) ≤ 17*workEnvelope L d := by
  have hc := expected_work_le_cap (μ := μ) hm L
  have hN := cap_pos L
  unfold workEnvelope
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 17)]
  apply le_min
  · linarith
  · by_cases hx : 1 ≤ cap L*d^2
    · have hlarge := (expected_work_survival_bound L hm hs).trans
        (finite_work_survival_bound L d hd hdmax hx)
      simpa [max_eq_right (Real.log_nonneg hx),mul_assoc] using hlarge
    · have hd2 := sq_pos_of_pos hd
      have hsmall : cap L ≤ (d⁻¹)^2 := by
        have h : cap L ≤ 1/d^2 := (le_div_iff₀ hd2).2 (by linarith)
        simpa [div_eq_mul_inv, inv_pow] using h
      have hn : 0 ≤ (d⁻¹)^2 := sq_nonneg _
      have hlog : 0 ≤ max 0 (Real.log (cap L*d^2)) := le_max_left _ _
      have hp := mul_nonneg hn hlog
      nlinarith

theorem expected_work_positive_bound (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1/2)
    (ht : HasMeanTails μ m (1/2+d)) :
    (∫ ω, work (fun k => m k ω) L ∂μ) ≤ 17*workEnvelope L d :=
  work_bound_of_survival L hd hdmax ht.measurable
    (fun k => survival_probability_positive L k hd ht)

theorem expected_work_negative_bound (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1/2)
    (ht : HasMeanTails μ m (1/2-d)) :
    (∫ ω, work (fun k => m k ω) L ∂μ) ≤ 17*workEnvelope L d :=
  work_bound_of_survival L hd hdmax ht.measurable
    (fun k => survival_probability_negative L k hd ht)

theorem decision_square_integral_le_one (hm : ∀ k, Measurable (m k)) (L : ℕ) :
    (∫ ω, (decision (fun k => m k ω) L)^2 ∂μ) ≤ 1 := by
  have heq : (fun ω => (decision (fun k => m k ω) L)^2) =
      fun ω => decision (fun k => m k ω) L := by
    funext ω
    rcases decision_zero_or_one (fun k => m k ω) L with h | h <;> simp [h]
  rw [heq]
  calc
    _ ≤ ∫ _ : Ω, (1:ℝ) ∂μ := integral_mono (integrable_decision m hm μ L)
      (integrable_const _) (fun ω => by
        rcases decision_zero_or_one (fun k => m k ω) L with h | h <;> simp [h])
    _ = 1 := by simp

theorem error_pair_bound (L : ℕ) {d : ℝ} (hd : 0 < d) :
    errorPrefactor/(cap (L+1)*d^2)^2 + errorPrefactor/(cap L*d^2)^2 ≤
      3/(cap (L+1)*d^2)^2 := by
  have hN := (cap_pos L).ne'
  have hdne := hd.ne'
  have hB : errorPrefactor ≤ 3/5 := errorPrefactor_le
  have heq : errorPrefactor/(cap (L+1)*d^2)^2 + errorPrefactor/(cap L*d^2)^2 =
      (5*errorPrefactor)/(cap (L+1)*d^2)^2 := by rw [cap_succ]; field_simp; ring
  rw [heq]
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

theorem increment_secondMoment_envelope (s : ℝ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1/2)
    (hm : ∀ k, Measurable (m k))
    (herr : ∀ L, μ.real {ω | decision (fun k => m k ω) L ≠ s} ≤
      errorPrefactor/(cap L*d^2)^2) (L : ℕ) :
    (∫ ω, (increment (fun k => decision (fun j => m j ω) k) L)^2 ∂μ) ≤
      min 1 (3/(cap L*d^2)^2) := by
  cases L with
  | zero =>
    simp only [increment,cap_zero,one_mul]
    apply le_min (decision_square_integral_le_one hm 0)
    apply (decision_square_integral_le_one hm 0).trans
    apply (le_div_iff₀ (sq_pos_of_pos (sq_pos_of_pos hd))).2
    have hds : d^2 ≤ 1/4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hds (sq_nonneg d)]
  | succ L =>
    simp only [increment]
    apply le_min (squared_decision_difference_le_one hm (L+1) L)
    exact ((squared_decision_difference_le_errors hm (L+1) L s).trans
      (add_le_add (herr (L+1)) (herr L))).trans (error_pair_bound L hd)

theorem increment_secondMoment_positive (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1/2)
    (ht : HasMeanTails μ m (1/2+d)) :
    (∫ ω, (increment (fun k => decision (fun j => m j ω) k) L)^2 ∂μ) ≤
      min 1 (3/(cap L*d^2)^2) :=
  increment_secondMoment_envelope 1 hd hdmax ht.measurable
    (fun L => error_positive_bound L hd ht) L

theorem increment_secondMoment_negative (L : ℕ) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1/2)
    (ht : HasMeanTails μ m (1/2-d)) :
    (∫ ω, (increment (fun k => decision (fun j => m j ω) k) L)^2 ∂μ) ≤
      min 1 (3/(cap L*d^2)^2) :=
  increment_secondMoment_envelope 0 hd hdmax ht.measurable
    (fun L => error_negative_bound L hd ht) L

end FinalBounds


end ThresholdHC.Tier2.Model

