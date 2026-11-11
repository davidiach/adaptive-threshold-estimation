import ThresholdHC.ArbitraryLawAdaptation.TailMedian
import ThresholdHC.ArbitraryLawAdaptation.TailProbeProbability

/-! Amplification of the tail probe by a median over independent probes.

`m` probes run on independent streams of fresh coins. A property that one
probe has with probability at least `3/4` holds for more than half of them
except with probability `exp(-m/8)`: the indicators of failure are independent
Bernoulli variables, and Hoeffding's inequality bounds the chance that half of
them fail. The median then inherits the property.

Applied to coverage and to the performance bound, a union bound gives both for
the median except with probability `2 exp(-m/8)`, which is at most `δ` when
`m ≥ 8 log(2/δ)`. The two properties are joined by a union bound and are not
assumed independent. A second union bound over depths, with failure allowance
`δ/(J(J+1))` at depth `J`, gives every depth at once. -/

noncomputable section
open MeasureTheory Real ProbabilityTheory
open scoped ENNReal
open Classical
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier2 ThresholdHC.Uniform713 ThresholdHC.EntropyTailUpper

section Blocks

variable {X : Type*} [MeasurableSpace X]

/-- The indicator bits of a set along a sequence of blocks. -/
def blockBits (B : Set X) (ω : ℕ → X) : ℕ → Bool := fun j => decide (ω j ∈ B)

theorem measurable_decide_mem {B : Set X} (hB : MeasurableSet B) :
    Measurable (fun x : X => decide (x ∈ B)) := by
  apply measurable_to_bool
  have h : (fun x : X => decide (x ∈ B)) ⁻¹' {true} = B := by
    ext x
    simp
  rw [h]
  exact hB

theorem measurable_blockBits {B : Set X} (hB : MeasurableSet B) : Measurable (blockBits B) :=
  Measurable.of_eval fun j => (measurable_decide_mem hB).comp (measurable_pi_apply j)

omit [MeasurableSpace X] in
/-- The number of ones among the first `m` indicator bits is the number of
the first `m` blocks in the set. -/
theorem tailHeads_blockBits (m : ℕ) (B : Set X) (ω : ℕ → X) :
    tailHeads m (blockBits B ω) = blockCount m (fun j => ω j ∈ B) := by
  unfold tailHeads blockBits blockCount
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : ω j ∈ B <;> simp [h]

/-- The indicator bit of a set of probability `p` is a Bernoulli variable. -/
theorem map_decide_mem (S : Measure X) [IsProbabilityMeasure S] {B : Set X}
    (hB : MeasurableSet B) :
    S.map (fun x : X => decide (x ∈ B)) =
      bernoulliMeasure true false ⟨S.real B, measureReal_nonneg, measureReal_le_one⟩ := by
  have hf := measurable_decide_mem hB
  apply eq_bernoulliMeasure
  · intro s hs ht hfl
    rw [Measure.map_apply hf hs]
    have h : (fun x : X => decide (x ∈ B)) ⁻¹' s = Set.univ := by
      ext x
      by_cases hx : x ∈ B <;> simp [hx, ht, hfl]
    rw [h, measure_univ]
  · intro s hs ht hfl
    rw [Measure.map_apply hf hs]
    have h : (fun x : X => decide (x ∈ B)) ⁻¹' s = B := by
      ext x
      by_cases hx : x ∈ B <;> simp [hx, ht, hfl]
    rw [h, ← ofReal_measureReal (μ := S) (s := B)]
    exact ENNReal.ofReal_eq_coe_nnreal measureReal_nonneg
  · intro s hs ht hfl
    rw [Measure.map_apply hf hs]
    have h : (fun x : X => decide (x ∈ B)) ⁻¹' s = Bᶜ := by
      ext x
      by_cases hx : x ∈ B <;> simp [hx, ht, hfl]
    have hnn : (0 : ℝ) ≤ 1 - S.real B := sub_nonneg.mpr measureReal_le_one
    rw [h, prob_compl_eq_one_sub hB, ← ofReal_measureReal (μ := S) (s := B),
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ measureReal_nonneg]
    exact ENNReal.ofReal_eq_coe_nnreal hnn
  · intro s hs ht hfl
    rw [Measure.map_apply hf hs]
    have h : (fun x : X => decide (x ∈ B)) ⁻¹' s = ∅ := by
      ext x
      by_cases hx : x ∈ B <;> simp [hx, ht, hfl]
    rw [h, measure_empty]

/-- Along independent blocks the indicator bits form a Bernoulli tape. -/
theorem blockBits_law (S : Measure X) [IsProbabilityMeasure S] {B : Set X}
    (hB : MeasurableSet B) :
    (Measure.infinitePi (fun _ : ℕ => S)).map (blockBits B) =
      tapeMeasure ⟨S.real B, measureReal_nonneg, measureReal_le_one⟩ := by
  unfold tapeMeasure blockBits
  rw [Measure.infinitePi_map_pi (f := fun _ (x : X) => decide (x ∈ B)) _
    (fun _ => measurable_decide_mem hB)]
  congr 1
  funext _
  exact map_decide_mem S hB

theorem measurableSet_blockMajority {B : Set X} (hB : MeasurableSet B) (m : ℕ) :
    MeasurableSet {ω : ℕ → X | m ≤ 2 * blockCount m (fun j => ω j ∈ B)} := by
  have h : {ω : ℕ → X | m ≤ 2 * blockCount m (fun j => ω j ∈ B)} =
      blockBits B ⁻¹' {t | m ≤ 2 * tailHeads m t} := by
    ext ω
    change m ≤ 2 * blockCount m (fun j => ω j ∈ B) ↔ m ≤ 2 * tailHeads m (blockBits B ω)
    rw [tailHeads_blockBits]
  rw [h]
  exact (measurable_blockBits hB) ((measurable_tailHeads m)
    (MeasurableSet.of_discrete (s := {n : ℕ | m ≤ 2 * n})))

/-- Hoeffding across independent blocks. A set of probability at most `1/4`
contains at least half of the first `m` blocks with probability at most
`exp(-m/8)`. -/
theorem blocks_fail_le (S : Measure X) [IsProbabilityMeasure S] {B : Set X}
    (hB : MeasurableSet B) (hp : S.real B ≤ 1 / 4) {m : ℕ} (hm : 0 < m) :
    (Measure.infinitePi (fun _ : ℕ => S)).real
      {ω | m ≤ 2 * blockCount m (fun j => ω j ∈ B)} ≤ exp (-(m : ℝ) / 8) := by
  have hmeas : MeasurableSet {t : ℕ → Bool | m ≤ 2 * tailHeads m t} :=
    (measurable_tailHeads m) (MeasurableSet.of_discrete (s := {n : ℕ | m ≤ 2 * n}))
  have hset : {ω : ℕ → X | m ≤ 2 * blockCount m (fun j => ω j ∈ B)} =
      blockBits B ⁻¹' {t | m ≤ 2 * tailHeads m t} := by
    ext ω
    change m ≤ 2 * blockCount m (fun j => ω j ∈ B) ↔ m ≤ 2 * tailHeads m (blockBits B ω)
    rw [tailHeads_blockBits]
  rw [hset, ← map_measureReal_apply (measurable_blockBits hB) hmeas, blockBits_law S hB]
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hsub : {t : ℕ → Bool | m ≤ 2 * tailHeads m t} ⊆
      {t | 1 / 2 - S.real B ≤ prefixMean observations m t - S.real B} := by
    intro t ht
    have h : m ≤ 2 * tailHeads m t := ht
    have hc : (m : ℝ) ≤ 2 * (tailHeads m t : ℝ) := by exact_mod_cast h
    have hhalf : (1 : ℝ) / 2 ≤ (tailHeads m t : ℝ) / m := by
      rw [le_div_iff₀ hm']
      linarith
    change 1 / 2 - S.real B ≤ prefixMean observations m t - S.real B
    rw [prefixMean_eq_heads]
    linarith
  have ht0 : (0 : ℝ) ≤ 1 / 2 - S.real B := by linarith
  have hquarter : (1 : ℝ) / 16 ≤ (1 / 2 - S.real B) ^ 2 := by nlinarith
  calc (tapeMeasure ⟨S.real B, measureReal_nonneg, measureReal_le_one⟩).real
        {t : ℕ → Bool | m ≤ 2 * tailHeads m t}
      ≤ (tapeMeasure ⟨S.real B, measureReal_nonneg, measureReal_le_one⟩).real
          {t | 1 / 2 - S.real B ≤ prefixMean observations m t - S.real B} :=
        measureReal_mono hsub
    _ ≤ exp (-2 * m * (1 / 2 - S.real B) ^ 2) :=
        tape_prefix_upper_tail ⟨S.real B, measureReal_nonneg, measureReal_le_one⟩ hm ht0
    _ ≤ exp (-(m : ℝ) / 8) := exp_le_exp.mpr (by nlinarith)

/-- A set of probability at least `3/4` contains more than half of the first
`m` independent blocks, except with probability `exp(-m/8)`. -/
theorem blocks_majority (S : Measure X) [IsProbabilityMeasure S] {G : Set X}
    (hG : MeasurableSet G) (hp : 3 / 4 ≤ S.real G) {m : ℕ} (hm : 0 < m) :
    (Measure.infinitePi (fun _ : ℕ => S)).real
      {ω | 2 * blockCount m (fun j => ω j ∈ G) ≤ m} ≤ exp (-(m : ℝ) / 8) := by
  have hc : S.real Gᶜ ≤ 1 / 4 := by
    rw [measureReal_compl hG, probReal_univ]
    linarith
  have hsub : {ω : ℕ → X | 2 * blockCount m (fun j => ω j ∈ G) ≤ m} ⊆
      {ω | m ≤ 2 * blockCount m (fun j => ω j ∈ Gᶜ)} := by
    intro ω hω
    have h : 2 * blockCount m (fun j => ω j ∈ G) ≤ m := hω
    have hadd := blockCount_add_not m (fun j => ω j ∈ G)
    have hle : blockCount m (fun j => ¬ ω j ∈ G) ≤ blockCount m (fun j => ω j ∈ Gᶜ) :=
      blockCount_mono fun j _ hj => hj
    change m ≤ 2 * blockCount m (fun j => ω j ∈ Gᶜ)
    omega
  exact (measureReal_mono hsub).trans (blocks_fail_le S hG.compl hc hm)

theorem measurableSet_blockMinority {G : Set X} (hG : MeasurableSet G) (m : ℕ) :
    MeasurableSet {ω : ℕ → X | 2 * blockCount m (fun j => ω j ∈ G) ≤ m} := by
  have h : {ω : ℕ → X | 2 * blockCount m (fun j => ω j ∈ G) ≤ m} =
      blockBits G ⁻¹' {t | 2 * tailHeads m t ≤ m} := by
    ext ω
    change 2 * blockCount m (fun j => ω j ∈ G) ≤ m ↔ 2 * tailHeads m (blockBits G ω) ≤ m
    rw [tailHeads_blockBits]
  rw [h]
  exact (measurable_blockBits hG) ((measurable_tailHeads m)
    (MeasurableSet.of_discrete (s := {n : ℕ | 2 * n ≤ m})))

end Blocks

/-- Streams on which one probe covers `F` at every flip budget and coin cap. -/
def probeValidSet (J : ℕ) (F : ℝ) : Set (ℕ → ℕ → Bool) :=
  {s | ∀ b M, F ≤ probeUpper (probeCompleted J b M s)}

/-- Streams on which one probe's certificate at budget `b` and coin cap `M` is
at most `c`. -/
def probeTightSet (J b M : ℕ) (c : ℝ) : Set (ℕ → ℕ → Bool) :=
  {s | probeUpper (probeCompleted J b M s) ≤ c}

/-- The failure event of the median certificate: at most half of the probes
cover `F` at every budget, or at most half meet the bound `c` at budget `b`
and coin cap `M`. -/
def medianFailure (J m b M : ℕ) (F c : ℝ) : Set (ℕ → ℕ → ℕ → Bool) :=
  {ω | 2 * blockCount m (fun j => ω j ∈ probeValidSet J F) ≤ m} ∪
    {ω | 2 * blockCount m (fun j => ω j ∈ probeTightSet J b M c) ≤ m}

theorem measurableSet_probeValidSet (J : ℕ) (F : ℝ) : MeasurableSet (probeValidSet J F) :=
  measurableSet_probeValid J F

theorem measurableSet_probeTightSet (J b M : ℕ) (c : ℝ) :
    MeasurableSet (probeTightSet J b M c) :=
  (measurable_probeCompleted J b M) (MeasurableSet.of_discrete (s := {n : ℕ | probeUpper n ≤ c}))

theorem measurableSet_medianFailure (J m b M : ℕ) (F c : ℝ) :
    MeasurableSet (medianFailure J m b M F c) :=
  (measurableSet_blockMinority (measurableSet_probeValidSet J F) m).union
    (measurableSet_blockMinority (measurableSet_probeTightSet J b M c) m)

/-- Outside the failure event the median covers `F` for every choice of flip
budgets and coin caps of the `m` probes, and with the common budget `b` and
coin cap `M` it is at most `c`. -/
theorem median_good_of_not_failure {J m b M : ℕ} {F c : ℝ} {ω : ℕ → ℕ → ℕ → Bool}
    (h : ω ∉ medianFailure J m b M F c) :
    (∀ b' M' : ℕ → ℕ, F ≤ medianUpper J m b' M' ω) ∧
      medianUpper J m (fun _ => b) (fun _ => M) ω ≤ c := by
  have h1 : m < 2 * blockCount m (fun j => ω j ∈ probeValidSet J F) :=
    not_le.mp fun hle => h (Or.inl hle)
  have h2 : m < 2 * blockCount m (fun j => ω j ∈ probeTightSet J b M c) :=
    not_le.mp fun hle => h (Or.inr hle)
  constructor
  · intro b' M'
    apply le_blockMedian
    have hmono : blockCount m (fun j => ω j ∈ probeValidSet J F) ≤
        blockCount m (fun j => F ≤ probeUpper (probeCompleted J (b' j) (M' j) (ω j))) :=
      blockCount_mono fun j _ hj => hj (b' j) (M' j)
    omega
  · apply blockMedian_le
    change m < 2 * blockCount m (fun j => probeUpper (probeCompleted J b M (ω j)) ≤ c)
    have hmono : blockCount m (fun j => ω j ∈ probeTightSet J b M c) ≤
        blockCount m (fun j => probeUpper (probeCompleted J b M (ω j)) ≤ c) :=
      blockCount_mono fun j _ hj => hj
    omega

section Amplify

variable (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν]

/-- The median certificate fails with probability at most `2 exp(-m/8)`. -/
theorem stream_medianFailure_le (J m b M : ℕ) (hm : 0 < m) (hb : 0 < b) (hM : 0 < M) {F W : ℝ}
    (hF1 : F ≤ 1) (hFu : F ≤ 2 * ν.real {t | tailUnresolved J t})
    (hW : ∫ t, (tailWork J t : ℝ) ∂ν ≤ W) :
    (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => ν))).real
      (medianFailure J m b M F
        (min 1 (128 * max (max (ν.real {t | tailUnresolved J t}) (W / b)) (1 / M)))) ≤
      2 * exp (-(m : ℝ) / 8) := by
  have hv : 3 / 4 ≤ (Measure.infinitePi (fun _ : ℕ => ν)).real (probeValidSet J F) := by
    have h := stream_probe_valid ν J hF1 hFu
    change 7 / 8 ≤ (Measure.infinitePi (fun _ : ℕ => ν)).real (probeValidSet J F) at h
    linarith
  have ht : 3 / 4 ≤ (Measure.infinitePi (fun _ : ℕ => ν)).real (probeTightSet J b M
      (min 1 (128 * max (max (ν.real {t | tailUnresolved J t}) (W / b)) (1 / M)))) :=
    stream_probe_performance ν J b M hb hM hW
  have h1 := blocks_majority (Measure.infinitePi (fun _ : ℕ => ν))
    (measurableSet_probeValidSet J F) hv hm
  have h2 := blocks_majority (Measure.infinitePi (fun _ : ℕ => ν))
    (measurableSet_probeTightSet J b M
      (min 1 (128 * max (max (ν.real {t | tailUnresolved J t}) (W / b)) (1 / M)))) ht hm
  unfold medianFailure
  have hu := measureReal_union_le
    (μ := Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => ν)))
    {ω | 2 * blockCount m (fun j => ω j ∈ probeValidSet J F) ≤ m}
    {ω | 2 * blockCount m (fun j => ω j ∈ probeTightSet J b M
      (min 1 (128 * max (max (ν.real {t | tailUnresolved J t}) (W / b)) (1 / M)))) ≤ m}
  linarith

/-- The median over `m` independent probes. Except with probability
`2 exp(-m/8)`, the median covers `F` for every choice of flip budgets and coin
caps of the probes, and with the common budget `b` and coin cap `M` it is at
most `min{1, 128 max(u, W/b, 1/M)}`. -/
theorem stream_median_certificate (J m b M : ℕ) (hm : 0 < m) (hb : 0 < b) (hM : 0 < M)
    {F W : ℝ} (hF1 : F ≤ 1) (hFu : F ≤ 2 * ν.real {t | tailUnresolved J t})
    (hW : ∫ t, (tailWork J t : ℝ) ∂ν ≤ W) :
    1 - 2 * exp (-(m : ℝ) / 8) ≤
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => ν))).real
        {ω | (∀ b' M' : ℕ → ℕ, F ≤ medianUpper J m b' M' ω) ∧
          medianUpper J m (fun _ => b) (fun _ => M) ω ≤
            min 1 (128 * max (max (ν.real {t | tailUnresolved J t}) (W / b)) (1 / M))} := by
  have hfail := stream_medianFailure_le ν J m b M hm hb hM hF1 hFu hW
  have hcover : (Set.univ : Set (ℕ → ℕ → ℕ → Bool)) ⊆
      {ω | (∀ b' M' : ℕ → ℕ, F ≤ medianUpper J m b' M' ω) ∧
        medianUpper J m (fun _ => b) (fun _ => M) ω ≤
          min 1 (128 * max (max (ν.real {t | tailUnresolved J t}) (W / b)) (1 / M))} ∪
        medianFailure J m b M F
          (min 1 (128 * max (max (ν.real {t | tailUnresolved J t}) (W / b)) (1 / M))) := by
    intro ω _
    by_cases h : ω ∈ medianFailure J m b M F
        (min 1 (128 * max (max (ν.real {t | tailUnresolved J t}) (W / b)) (1 / M)))
    · exact Or.inr h
    · exact Or.inl (median_good_of_not_failure h)
  have h1 := measureReal_mono
    (μ := Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => ν))) hcover
  rw [probReal_univ] at h1
  have h2 := measureReal_union_le
    (μ := Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => ν)))
    {ω | (∀ b' M' : ℕ → ℕ, F ≤ medianUpper J m b' M' ω) ∧
      medianUpper J m (fun _ => b) (fun _ => M) ω ≤
        min 1 (128 * max (max (ν.real {t | tailUnresolved J t}) (W / b)) (1 / M))}
    (medianFailure J m b M F
      (min 1 (128 * max (max (ν.real {t | tailUnresolved J t}) (W / b)) (1 / M))))
  linarith

end Amplify

/-- The calibration of the number of probes: `2 exp(-m/8) ≤ δ` when
`m ≥ 8 log(2/δ)`. -/
theorem two_exp_le_of_log_le {δ : ℝ} (hδ : 0 < δ) {m : ℕ} (hm : 8 * log (2 / δ) ≤ m) :
    2 * exp (-(m : ℝ) / 8) ≤ δ := by
  have hpos : (0 : ℝ) < 2 / δ := by positivity
  have hle : exp (-(m : ℝ) / 8) ≤ exp (-log (2 / δ)) := exp_le_exp.mpr (by linarith)
  rw [exp_neg, exp_log hpos, inv_div] at hle
  linarith

/-- The failure allowances `δ/(J(J+1))` of the depths sum to at most `δ`. -/
theorem depth_weight_sum_le {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    ∑ J ∈ Finset.range n, δ / ((J : ℝ) * (J + 1)) ≤ δ := by
  have heq : ∀ n : ℕ, ∑ J ∈ Finset.range (n + 1), δ / ((J : ℝ) * (J + 1)) =
      δ * (1 - 1 / (n + 1)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((n : ℝ) + 1 + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  rcases n with _ | n
  · simpa using hδ
  · rw [heq n]
    have hfrac : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    nlinarith

/-- A union bound over depths on independent coordinates. If the failure event
of depth `J ≥ 1` has probability at most `δ/(J(J+1))`, then some depth fails
with probability at most `δ`. -/
theorem depth_union_bound {Y : Type*} [MeasurableSpace Y] (P : Measure Y)
    [IsProbabilityMeasure P] (Bad : ℕ → Set Y) (hmeas : ∀ J, MeasurableSet (Bad J)) {δ : ℝ}
    (hδ : 0 ≤ δ) (hbad : ∀ J, 1 ≤ J → P.real (Bad J) ≤ δ / ((J : ℝ) * (J + 1))) :
    (Measure.infinitePi (fun _ : ℕ => P)).real {ω | ∃ J, 1 ≤ J ∧ ω J ∈ Bad J} ≤ δ := by
  have hset : {ω : ℕ → Y | ∃ J, 1 ≤ J ∧ ω J ∈ Bad J} =
      ⋃ J, {ω : ℕ → Y | 1 ≤ J ∧ ω J ∈ Bad J} := by
    ext ω
    simp
  have hterm : ∀ J, (Measure.infinitePi (fun _ : ℕ => P)) {ω : ℕ → Y | 1 ≤ J ∧ ω J ∈ Bad J} ≤
      ENNReal.ofReal (δ / ((J : ℝ) * (J + 1))) := by
    intro J
    by_cases hJ : 1 ≤ J
    · have heq : {ω : ℕ → Y | 1 ≤ J ∧ ω J ∈ Bad J} = (fun ω : ℕ → Y => ω J) ⁻¹' Bad J := by
        ext ω
        simp [hJ]
      rw [heq, ← Measure.map_apply (measurable_pi_apply J) (hmeas J),
        Measure.infinitePi_map_eval, ← ofReal_measureReal (μ := P) (s := Bad J)]
      exact ENNReal.ofReal_le_ofReal (hbad J hJ)
    · have heq : {ω : ℕ → Y | 1 ≤ J ∧ ω J ∈ Bad J} = ∅ := by
        ext ω
        simp [hJ]
      rw [heq, measure_empty]
      exact zero_le
  apply ENNReal.toReal_le_of_le_ofReal hδ
  rw [hset]
  calc (Measure.infinitePi (fun _ : ℕ => P)) (⋃ J, {ω : ℕ → Y | 1 ≤ J ∧ ω J ∈ Bad J})
      ≤ ∑' J, (Measure.infinitePi (fun _ : ℕ => P)) {ω : ℕ → Y | 1 ≤ J ∧ ω J ∈ Bad J} :=
        measure_iUnion_le _
    _ ≤ ∑' J : ℕ, ENNReal.ofReal (δ / ((J : ℝ) * (J + 1))) := ENNReal.tsum_le_tsum hterm
    _ ≤ ENNReal.ofReal δ := by
        apply ENNReal.tsum_le_of_sum_range_le
        intro n
        rw [← ENNReal.ofReal_sum_of_nonneg fun J _ => by positivity]
        exact ENNReal.ofReal_le_ofReal (depth_weight_sum_le hδ n)

end ThresholdHC.ArbitraryLawAdaptation
