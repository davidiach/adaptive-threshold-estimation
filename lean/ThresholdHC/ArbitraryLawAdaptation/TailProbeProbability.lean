import ThresholdHC.ArbitraryLawAdaptation.TailProbe
import ThresholdHC.ArbitraryLawAdaptation.TailTestProbability

/-! Probability bounds for one tail probe on a stream of independent coins.

The stream has law `Measure.infinitePi (fun _ => ν)`: independent fresh coins
whose tapes share an arbitrary probability law `ν`. Write `u` for the
probability that the tail test leaves one coin unresolved.

* Validity. If `F ≤ 1` and `F ≤ 2u`, then with probability at least `7/8`
  the certificate is at least `F` at every flip budget and every coin cap
  simultaneously. The proof bounds the event that the first `⌊4/u⌋` coins are
  all resolved; it never treats the number of completed coins as a fixed
  sample size.
* Performance. At a fixed budget `b` and coin cap `M`, with probability at
  least `3/4` the certificate is at most `min{1, 128 max(u, W/b, 1/M)}` for
  every `W` that bounds the expected work of one coin. The two failure events,
  an unresolved coin among the first `q` and their combined work exceeding
  `b`, are joined by a union bound and are not assumed independent. -/

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawAdaptation

theorem measurable_probeWork (J n : ℕ) :
    Measurable (fun ω : ℕ → ℕ → Bool => probeWork J ω n) := by
  unfold probeWork
  exact Finset.measurable_sum _ fun i _ => (measurable_tailWork J).comp (measurable_pi_apply i)

theorem measurable_streamUnresolved (J i : ℕ) :
    Measurable (fun ω : ℕ → ℕ → Bool => tailUnresolved J (ω i)) :=
  measurableSet_setOfPred.1
    (show MeasurableSet {ω : ℕ → ℕ → Bool | tailUnresolved J (ω i)} from
      (measurableSet_tailUnresolved J).preimage (measurable_pi_apply i))

theorem measurableSet_probeAdmits (J M n : ℕ) :
    MeasurableSet {ω : ℕ → ℕ → Bool | probeAdmits J M ω n} :=
  Measurable.setOf (measurable_const.and (Measurable.forall fun i =>
    measurable_const.imp (measurable_streamUnresolved J i).not))

theorem measurableSet_probeReaches (J b M n : ℕ) :
    MeasurableSet {ω : ℕ → ℕ → Bool | probeReaches J b M ω n} :=
  (measurableSet_probeAdmits J M n).inter ((measurable_probeWork J n) measurableSet_Iic)

/-- The completed count is a measurable function of the stream. -/
theorem measurable_probeCompleted (J b M : ℕ) : Measurable (probeCompleted J b M) := by
  refine measurable_of_Ici fun n => ?_
  have h : probeCompleted J b M ⁻¹' Set.Ici n = {ω | probeReaches J b M ω n} := by
    ext ω
    exact le_probeCompleted_iff J b M ω n
  rw [h]
  exact measurableSet_probeReaches J b M n

/-- The event that the certificate is valid at every budget and every coin
cap is measurable. -/
theorem measurableSet_probeValid (J : ℕ) (F : ℝ) :
    MeasurableSet {ω : ℕ → ℕ → Bool | ∀ b M, F ≤ probeUpper (probeCompleted J b M ω)} :=
  Measurable.setOf (Measurable.forall fun b => Measurable.forall fun M =>
    measurableSet_setOfPred.1 ((measurable_probeCompleted J b M)
      (MeasurableSet.of_discrete (s := {n : ℕ | F ≤ probeUpper n}))))

section Stream

variable (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν]

/-- One coin of the stream has law `ν`. -/
theorem stream_eval_real (i : ℕ) {S : Set (ℕ → Bool)} (hS : MeasurableSet S) :
    (Measure.infinitePi (fun _ : ℕ => ν)).real {ω | ω i ∈ S} = ν.real S := by
  calc (Measure.infinitePi (fun _ : ℕ => ν)).real {ω | ω i ∈ S}
      = ((Measure.infinitePi (fun _ : ℕ => ν)).map (fun x => x i)).real S :=
        (map_measureReal_apply (measurable_pi_apply i) hS).symm
    _ = ν.real S := by rw [Measure.infinitePi_map_eval]

theorem stream_eval_integral (i : ℕ) (G : (ℕ → Bool) → ℝ) (hG : Measurable G) :
    ∫ ω, G (ω i) ∂Measure.infinitePi (fun _ : ℕ => ν) = ∫ t, G t ∂ν := by
  calc ∫ ω, G (ω i) ∂Measure.infinitePi (fun _ : ℕ => ν)
      = ∫ t, G t ∂(Measure.infinitePi (fun _ : ℕ => ν)).map (fun x => x i) :=
        (integral_map (measurable_pi_apply i).aemeasurable hG.aestronglyMeasurable).symm
    _ = ∫ t, G t ∂ν := by rw [Measure.infinitePi_map_eval]

/-- Independence of fresh coins: the first `m` coins are all resolved with
probability `(1 - u)^m`. -/
theorem stream_all_resolved (J m : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).real {ω | ∀ i < m, ¬ tailUnresolved J (ω i)} =
      (1 - ν.real {t | tailUnresolved J t}) ^ m := by
  have hS : MeasurableSet {t : ℕ → Bool | ¬ tailUnresolved J t} :=
    (measurableSet_tailUnresolved J).compl
  have hset : {ω : ℕ → ℕ → Bool | ∀ i < m, ¬ tailUnresolved J (ω i)} =
      Set.pi (Finset.range m : Set ℕ) (fun _ => {t : ℕ → Bool | ¬ tailUnresolved J t}) := by
    ext ω
    simp [Set.pi]
  have hone : (ν {t : ℕ → Bool | ¬ tailUnresolved J t}).toReal =
      1 - ν.real {t | tailUnresolved J t} := by
    have h := measureReal_compl (μ := ν) (measurableSet_tailUnresolved J)
    rw [probReal_univ] at h
    exact h
  have hpi := Measure.infinitePi_pi (μ := fun _ : ℕ => ν) (s := Finset.range m)
    (t := fun _ => {t : ℕ → Bool | ¬ tailUnresolved J t}) (fun _ _ => hS)
  rw [hset, measureReal_def, hpi, Finset.prod_const, Finset.card_range, ENNReal.toReal_pow, hone]

/-- A union bound: some coin among the first `q` is unresolved with
probability at most `q u`. -/
theorem stream_some_unresolved_le (J q : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).real {ω | ∃ i < q, tailUnresolved J (ω i)} ≤
      q * ν.real {t | tailUnresolved J t} := by
  have hset : {ω : ℕ → ℕ → Bool | ∃ i < q, tailUnresolved J (ω i)} =
      ⋃ i ∈ Finset.range q, {ω | ω i ∈ {t : ℕ → Bool | tailUnresolved J t}} := by
    ext ω
    simp
  rw [hset]
  calc (Measure.infinitePi (fun _ : ℕ => ν)).real
        (⋃ i ∈ Finset.range q, {ω | ω i ∈ {t : ℕ → Bool | tailUnresolved J t}})
      ≤ ∑ i ∈ Finset.range q, (Measure.infinitePi (fun _ : ℕ => ν)).real
          {ω | ω i ∈ {t : ℕ → Bool | tailUnresolved J t}} :=
        measureReal_biUnion_finset_le _ _
    _ = ∑ _i ∈ Finset.range q, ν.real {t | tailUnresolved J t} :=
        Finset.sum_congr rfl fun i _ => stream_eval_real ν i (measurableSet_tailUnresolved J)
    _ = q * ν.real {t | tailUnresolved J t} := by simp

theorem integrable_probeWork (J q : ℕ) :
    Integrable (fun ω : ℕ → ℕ → Bool => (probeWork J ω q : ℝ))
      (Measure.infinitePi (fun _ : ℕ => ν)) :=
  ThresholdHC.Tier5.integrable_of_abs_bound _ _
    ((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (measurable_probeWork J q))
    (q * 4 ^ J) fun ω => by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast probeWork_le J ω q

/-- Linearity: the first `q` coins cost `q` times the expected work of one. -/
theorem stream_expected_work (J q : ℕ) :
    ∫ ω, (probeWork J ω q : ℝ) ∂Measure.infinitePi (fun _ : ℕ => ν) =
      q * ∫ t, (tailWork J t : ℝ) ∂ν := by
  have hm : Measurable (fun t : ℕ → Bool => (tailWork J t : ℝ)) :=
    (measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (measurable_tailWork J)
  have hi : ∀ i ∈ Finset.range q, Integrable (fun ω : ℕ → ℕ → Bool => (tailWork J (ω i) : ℝ))
      (Measure.infinitePi (fun _ : ℕ => ν)) := fun i _ =>
    ThresholdHC.Tier5.integrable_of_abs_bound _ _ (hm.comp (measurable_pi_apply i)) (4 ^ J)
      fun ω => by
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast tailWork_le J (ω i)
  have hsum : (fun ω : ℕ → ℕ → Bool => (probeWork J ω q : ℝ)) =
      fun ω => ∑ i ∈ Finset.range q, (tailWork J (ω i) : ℝ) := by
    funext ω
    unfold probeWork
    push_cast
    rfl
  rw [hsum, integral_finsetSum _ hi]
  calc ∑ i ∈ Finset.range q, ∫ ω, (tailWork J (ω i) : ℝ) ∂Measure.infinitePi (fun _ : ℕ => ν)
      = ∑ _i ∈ Finset.range q, ∫ t, (tailWork J t : ℝ) ∂ν :=
        Finset.sum_congr rfl fun i _ => stream_eval_integral ν i _ hm
    _ = q * ∫ t, (tailWork J t : ℝ) ∂ν := by simp

/-- Markov's inequality for the combined work of the first `q` coins. -/
theorem stream_work_exceeds_le (J q b : ℕ) (hb : 0 < b) :
    (Measure.infinitePi (fun _ : ℕ => ν)).real {ω | b < probeWork J ω q} ≤
      q * (∫ t, (tailWork J t : ℝ) ∂ν) / b := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (μ := Measure.infinitePi (fun _ : ℕ => ν)) (f := fun ω => (probeWork J ω q : ℝ))
    (ae_of_all _ fun ω => Nat.cast_nonneg _) (integrable_probeWork ν J q) (b : ℝ)
  rw [stream_expected_work] at hmk
  have hsub : {ω : ℕ → ℕ → Bool | b < probeWork J ω q} ⊆
      {ω | (b : ℝ) ≤ (probeWork J ω q : ℝ)} := fun ω hω => by
    have h : b < probeWork J ω q := hω
    exact_mod_cast h.le
  have hmono := measureReal_mono (μ := Measure.infinitePi (fun _ : ℕ => ν)) hsub
  rw [le_div_iff₀ hb']
  calc (Measure.infinitePi (fun _ : ℕ => ν)).real {ω | b < probeWork J ω q} * b
      ≤ (Measure.infinitePi (fun _ : ℕ => ν)).real {ω | (b : ℝ) ≤ (probeWork J ω q : ℝ)} * b :=
        mul_le_mul_of_nonneg_right hmono hb'.le
    _ = b * (Measure.infinitePi (fun _ : ℕ => ν)).real
          {ω | (b : ℝ) ≤ (probeWork J ω q : ℝ)} := mul_comm _ _
    _ ≤ q * ∫ t, (tailWork J t : ℝ) ∂ν := hmk

end Stream

/-- A certificate below `F`, where `F ≤ 1` and `F ≤ 2u`, forces `u > 0` and
the first `⌊4/u⌋` coins to be resolved. -/
theorem resolved_prefix_of_upper_lt {J b M : ℕ} {ω : ℕ → ℕ → Bool} {F u : ℝ} (hF1 : F ≤ 1)
    (hFu : F ≤ 2 * u) (h : probeUpper (probeCompleted J b M ω) < F) :
    0 < u ∧ ∀ i < ⌊4 / u⌋₊, ¬ tailUnresolved J (ω i) := by
  have hreach := (probeCompleted_reaches J b M ω).1.2
  obtain ⟨n, hn⟩ : ∃ n, probeCompleted J b M ω = n := ⟨_, rfl⟩
  rw [hn] at h hreach
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0, probeUpper_zero] at h
    linarith
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have h8 : 8 / (n : ℝ) < F := by
    unfold probeUpper at h
    rw [ite_eq_right hn0] at h
    rcases min_lt_iff.mp h with h1 | h2
    · linarith
    · exact h2
  have h8' : 8 < F * n := by rwa [div_lt_iff₀ hnpos] at h8
  have hu : 0 < u := by
    by_contra hc
    have hu0 : u ≤ 0 := not_lt.mp hc
    have hF0 : F ≤ 0 := by linarith
    nlinarith
  refine ⟨hu, fun i hi => ?_⟩
  have h4 : 4 / u < n := by
    rw [div_lt_iff₀ hu]
    nlinarith
  have hfl : (⌊4 / u⌋₊ : ℝ) ≤ 4 / u := Nat.floor_le (by positivity)
  have hlt : ⌊4 / u⌋₊ < n := by exact_mod_cast hfl.trans_lt h4
  exact hreach i (by omega)

theorem exp_neg_three_le : exp (-3) ≤ 1 / 8 := by
  have h2 : (2 : ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
  have h3 : exp 3 = exp 1 * exp 1 * exp 1 := by
    rw [← exp_add, ← exp_add]
    norm_num
  have h8 : (8 : ℝ) < exp 3 := by
    rw [h3]
    nlinarith [exp_pos 1]
  have hprod : exp (-3) * exp 3 = 1 := by
    rw [← exp_add]
    simp
  nlinarith [exp_pos (-3)]

section Guarantees

variable (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν]

/-- The certificate falls below `F` at some budget and coin cap with
probability at most `1/8`. -/
theorem stream_probe_invalid_le (J : ℕ) {F : ℝ} (hF1 : F ≤ 1)
    (hFu : F ≤ 2 * ν.real {t | tailUnresolved J t}) :
    (Measure.infinitePi (fun _ : ℕ => ν)).real
      {ω | ∃ b M, probeUpper (probeCompleted J b M ω) < F} ≤ 1 / 8 := by
  obtain ⟨u, hu_def⟩ : ∃ u, ν.real {t | tailUnresolved J t} = u := ⟨_, rfl⟩
  rw [hu_def] at hFu
  have hu1 : u ≤ 1 := hu_def ▸ measureReal_le_one
  by_cases hu : 0 < u
  · have hsub : {ω : ℕ → ℕ → Bool | ∃ b M, probeUpper (probeCompleted J b M ω) < F} ⊆
        {ω | ∀ i < ⌊4 / u⌋₊, ¬ tailUnresolved J (ω i)} := by
      rintro ω ⟨b, M, h⟩
      exact (resolved_prefix_of_upper_lt hF1 hFu h).2
    have hfloor : 4 / u < ⌊4 / u⌋₊ + 1 := Nat.lt_floor_add_one _
    have hmul : 3 ≤ (⌊4 / u⌋₊ : ℝ) * u := by
      have h4 : 4 < ((⌊4 / u⌋₊ : ℝ) + 1) * u := by rwa [div_lt_iff₀ hu] at hfloor
      linarith
    calc (Measure.infinitePi (fun _ : ℕ => ν)).real
          {ω | ∃ b M, probeUpper (probeCompleted J b M ω) < F}
        ≤ (Measure.infinitePi (fun _ : ℕ => ν)).real
            {ω | ∀ i < ⌊4 / u⌋₊, ¬ tailUnresolved J (ω i)} := measureReal_mono hsub
      _ = (1 - u) ^ ⌊4 / u⌋₊ := by rw [stream_all_resolved ν J _, hu_def]
      _ ≤ exp (-u) ^ ⌊4 / u⌋₊ :=
          pow_le_pow_left₀ (by linarith) (by linarith [add_one_le_exp (-u)]) _
      _ = exp ((⌊4 / u⌋₊ : ℝ) * -u) := (Real.exp_nat_mul _ _).symm
      _ ≤ exp (-3) := exp_le_exp.mpr (by linarith)
      _ ≤ 1 / 8 := exp_neg_three_le
  · have hempty : {ω : ℕ → ℕ → Bool | ∃ b M, probeUpper (probeCompleted J b M ω) < F} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨b, M, h⟩
      exact hu (resolved_prefix_of_upper_lt hF1 hFu h).1
    rw [hempty]
    simp

/-- Validity at every budget simultaneously. If `F ≤ 1` and `F ≤ 2u`, then
with probability at least `7/8` the certificate is at least `F` at every flip
budget and every coin cap. -/
theorem stream_probe_valid (J : ℕ) {F : ℝ} (hF1 : F ≤ 1)
    (hFu : F ≤ 2 * ν.real {t | tailUnresolved J t}) :
    7 / 8 ≤ (Measure.infinitePi (fun _ : ℕ => ν)).real
      {ω | ∀ b M, F ≤ probeUpper (probeCompleted J b M ω)} := by
  have hcover : (Set.univ : Set (ℕ → ℕ → Bool)) ⊆
      {ω | ∀ b M, F ≤ probeUpper (probeCompleted J b M ω)} ∪
        {ω | ∃ b M, probeUpper (probeCompleted J b M ω) < F} := by
    intro ω _
    by_cases h : ∀ b M, F ≤ probeUpper (probeCompleted J b M ω)
    · exact Or.inl h
    · push Not at h
      exact Or.inr h
  have h1 := measureReal_mono (μ := Measure.infinitePi (fun _ : ℕ => ν)) hcover
  rw [probReal_univ] at h1
  have h2 := measureReal_union_le (μ := Measure.infinitePi (fun _ : ℕ => ν))
    {ω | ∀ b M, F ≤ probeUpper (probeCompleted J b M ω)}
    {ω | ∃ b M, probeUpper (probeCompleted J b M ω) < F}
  linarith [stream_probe_invalid_le ν J hF1 hFu]

/-- Performance at a fixed budget. For every flip budget `b ≥ 1`, coin cap
`M ≥ 1` and bound `W` on the expected work of one coin, with probability at
least `3/4` the certificate is at most `min{1, 128 max(u, W/b, 1/M)}`. -/
theorem stream_probe_performance (J b M : ℕ) (hb : 0 < b) (hM : 0 < M) {W : ℝ}
    (hW : ∫ t, (tailWork J t : ℝ) ∂ν ≤ W) :
    3 / 4 ≤ (Measure.infinitePi (fun _ : ℕ => ν)).real
      {ω | probeUpper (probeCompleted J b M ω) ≤
        min 1 (128 * max (max (ν.real {t | tailUnresolved J t}) (W / b)) (1 / M))} := by
  obtain ⟨u, hu_def⟩ : ∃ u, ν.real {t | tailUnresolved J t} = u := ⟨_, rfl⟩
  obtain ⟨w, hw_def⟩ : ∃ w, ∫ t, (tailWork J t : ℝ) ∂ν = w := ⟨_, rfl⟩
  have hsome := fun q => stream_some_unresolved_le ν J q
  have hexceed := fun q => stream_work_exceeds_le ν J q b hb
  simp only [hu_def, hw_def] at hsome hexceed hW ⊢
  have hu0 : 0 ≤ u := hu_def ▸ measureReal_nonneg
  have hw0 : 0 ≤ w := hw_def ▸ integral_nonneg fun t => Nat.cast_nonneg _
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hM' : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  obtain ⟨A, hA⟩ : ∃ A, max (max u (W / b)) (1 / (M : ℝ)) = A := ⟨_, rfl⟩
  rw [hA]
  have hAu : u ≤ A := hA ▸ (le_max_left _ _).trans (le_max_left _ _)
  have hAW : W / b ≤ A := hA ▸ (le_max_right _ _).trans (le_max_left _ _)
  have hAM : 1 / (M : ℝ) ≤ A := hA ▸ le_max_right _ _
  have hApos : 0 < A := lt_of_lt_of_le (by positivity) hAM
  have hWb : 0 ≤ W / b := div_nonneg (hw0.trans hW) hb'.le
  by_cases hbig : 1 / 16 ≤ A
  · have hall : {ω : ℕ → ℕ → Bool | probeUpper (probeCompleted J b M ω) ≤ min 1 (128 * A)} =
        Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      rw [min_eq_left (by linarith)]
      exact probeUpper_le_one _
    rw [hall, probReal_univ]
    norm_num
  · have hsmall : A < 1 / 16 := not_le.mp hbig
    obtain ⟨x, hx⟩ : ∃ x, 1 / (8 * A) = x := ⟨_, rfl⟩
    have hxA : x * A = 1 / 8 := by
      rw [← hx]
      field_simp
    have hx2 : 2 < x := by nlinarith
    obtain ⟨q, hq⟩ : ∃ q, ⌊x⌋₊ = q := ⟨_, rfl⟩
    have hqle : (q : ℝ) ≤ x := hq ▸ Nat.floor_le (by linarith)
    have hqlt : x < q + 1 := hq ▸ Nat.lt_floor_add_one x
    have hqpos : 0 < q := by
      have h : (0 : ℝ) < q := by linarith
      exact_mod_cast h
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hE1 : (Measure.infinitePi (fun _ : ℕ => ν)).real
        {ω | ∃ i < q, tailUnresolved J (ω i)} ≤ 1 / 8 :=
      calc _ ≤ q * u := hsome q
        _ ≤ x * A := mul_le_mul hqle hAu hu0 (by linarith)
        _ = 1 / 8 := hxA
    have hE2 : (Measure.infinitePi (fun _ : ℕ => ν)).real
        {ω | b < probeWork J ω q} ≤ 1 / 8 :=
      calc _ ≤ q * w / b := hexceed q
        _ = q * (w / b) := mul_div_assoc _ _ _
        _ ≤ q * (W / b) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hW hb'.le) hq0
        _ ≤ x * A := mul_le_mul hqle hAW hWb (by linarith)
        _ = 1 / 8 := hxA
    have hqM : q ≤ M := by
      have h1 : 1 ≤ A * M := by rwa [div_le_iff₀ hM'] at hAM
      have h2 : (q : ℝ) ≤ M := by nlinarith
      exact_mod_cast h2
    have hAq : 1 / 16 ≤ A * q := by nlinarith
    have hcover : (Set.univ : Set (ℕ → ℕ → Bool)) ⊆
        {ω | probeUpper (probeCompleted J b M ω) ≤ min 1 (128 * A)} ∪
          ({ω | ∃ i < q, tailUnresolved J (ω i)} ∪ {ω | b < probeWork J ω q}) := by
      intro ω _
      by_cases h1 : ∃ i < q, tailUnresolved J (ω i)
      · exact Or.inr (Or.inl h1)
      by_cases h2 : b < probeWork J ω q
      · exact Or.inr (Or.inr h2)
      left
      push Not at h1
      have hreach : probeReaches J b M ω q :=
        ⟨⟨hqM, fun i hi => h1 i (by omega)⟩, not_lt.mp h2⟩
      have hle : q ≤ probeCompleted J b M ω := (le_probeCompleted_iff J b M ω q).2 hreach
      refine le_min (probeUpper_le_one _) ?_
      have hqpos' : (0 : ℝ) < q := Nat.cast_pos.mpr hqpos
      calc probeUpper (probeCompleted J b M ω) ≤ probeUpper q := probeUpper_antitone hle
        _ ≤ 8 / q := probeUpper_le_div hqpos
        _ ≤ 128 * A := by
            rw [div_le_iff₀ hqpos']
            nlinarith
    have h1 := measureReal_mono (μ := Measure.infinitePi (fun _ : ℕ => ν)) hcover
    rw [probReal_univ] at h1
    have h2 := measureReal_union_le (μ := Measure.infinitePi (fun _ : ℕ => ν))
      {ω | probeUpper (probeCompleted J b M ω) ≤ min 1 (128 * A)}
      ({ω | ∃ i < q, tailUnresolved J (ω i)} ∪ {ω | b < probeWork J ω q})
    have h3 := measureReal_union_le (μ := Measure.infinitePi (fun _ : ℕ => ν))
      {ω | ∃ i < q, tailUnresolved J (ω i)} {ω | b < probeWork J ω q}
    linarith

end Guarantees

end ThresholdHC.ArbitraryLawAdaptation
