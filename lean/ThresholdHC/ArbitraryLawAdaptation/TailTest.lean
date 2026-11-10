import ThresholdHC.EntropyTailUpper.PrefixConcentration

/-! The sign-neutral single-coin tail test of the arbitrary-law tail certificate.

One persistent coin is inspected after `n_k = 4^k` flips, `k = 0,…,J`. Check `k`
resolves the coin when `|X̄_{n_k} - 1/2| > h_k/n_k` with the integer threshold
`h_k = ⌈√(2 n_k (J-k+2))⌉`; a tie continues. The coin is unresolved when the
terminal check also fails. This module defines the test on a tape of flips and
proves its deterministic properties: the work cap, dependence on the observed
prefix only, and invariance under complementing every flip. No probability
enters here. -/

noncomputable section
open MeasureTheory
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier2 ThresholdHC.Uniform713

/-- Heads among the first `n` flips of a tape. -/
def tailHeads (n : ℕ) (ω : ℕ → Bool) : ℕ := ∑ i ∈ Finset.range n, (ω i).toNat

/-- The quantity `2 n_k (J-k+2)` at the checkpoint `n_k = 4^k`. -/
def tailScale (J k : ℕ) : ℕ := 2 * 4 ^ k * (J - k + 2)

/-- The integer threshold `h_k = ⌈√(2 n_k (J-k+2))⌉`. -/
def tailThreshold (J k : ℕ) : ℕ := ⌈Real.sqrt (tailScale J k)⌉₊

/-- Check `k` resolves the coin: `|X̄ - 1/2| > h_k/n_k`, written with integers as
`|2S - n_k| > 2 h_k`. The inequality is strict, so a tie does not resolve. -/
def tailResolvedAt (J k : ℕ) (ω : ℕ → Bool) : Prop :=
  2 * (tailThreshold J k : ℤ) < |2 * (tailHeads (4 ^ k) ω : ℤ) - ((4 ^ k : ℕ) : ℤ)|

/-- No check up to and including the terminal one resolves the coin. -/
def tailUnresolved (J : ℕ) (ω : ℕ → Bool) : Prop := ∀ k, k ≤ J → ¬ tailResolvedAt J k ω

/-- The stopping check: the first resolving check, and the terminal check `J`
when there is none. -/
def tailStop (J : ℕ) (ω : ℕ → Bool) : ℕ := sInf {k | J ≤ k ∨ tailResolvedAt J k ω}

/-- Flips bought on the coin. -/
def tailWork (J : ℕ) (ω : ℕ → Bool) : ℕ := 4 ^ tailStop J ω

/-- Complement every flip. -/
def tapeFlip (ω : ℕ → Bool) : ℕ → Bool := fun i => !ω i

theorem tailHeads_le (n : ℕ) (ω : ℕ → Bool) : tailHeads n ω ≤ n := by
  unfold tailHeads
  calc ∑ i ∈ Finset.range n, (ω i).toNat ≤ ∑ _i ∈ Finset.range n, 1 :=
        Finset.sum_le_sum fun i _ => Bool.toNat_le (ω i)
    _ = n := by simp

theorem tailHeads_congr {n : ℕ} {ω ω' : ℕ → Bool} (h : ∀ i < n, ω i = ω' i) :
    tailHeads n ω = tailHeads n ω' := by
  unfold tailHeads
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]

theorem tailHeads_flip (n : ℕ) (ω : ℕ → Bool) :
    tailHeads n (tapeFlip ω) = n - tailHeads n ω := by
  have h : tailHeads n (tapeFlip ω) + tailHeads n ω = n := by
    unfold tailHeads tapeFlip
    rw [← Finset.sum_add_distrib]
    calc ∑ i ∈ Finset.range n, ((!ω i).toNat + (ω i).toNat)
        = ∑ _i ∈ Finset.range n, 1 :=
          Finset.sum_congr rfl fun i _ => by cases ω i <;> rfl
      _ = n := by simp
  omega

/-- The mean of the first `n` observations is the head count over `n`. -/
theorem prefixMean_eq_heads (n : ℕ) (ω : ℕ → Bool) :
    prefixMean observations n ω = (tailHeads n ω : ℝ) / n := by
  unfold prefixMean tailHeads observations
  rw [Nat.cast_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by cases ω i <;> simp [bit]

theorem tailScale_le_threshold_sq (J k : ℕ) :
    (tailScale J k : ℝ) ≤ (tailThreshold J k : ℝ) ^ 2 := by
  have h : Real.sqrt (tailScale J k) ≤ (tailThreshold J k : ℝ) := Nat.le_ceil _
  calc (tailScale J k : ℝ) = Real.sqrt (tailScale J k) ^ 2 :=
        (Real.sq_sqrt (Nat.cast_nonneg _)).symm
    _ ≤ (tailThreshold J k : ℝ) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

theorem tailThreshold_lt (J k : ℕ) :
    (tailThreshold J k : ℝ) < Real.sqrt (tailScale J k) + 1 :=
  Nat.ceil_lt_add_one (Real.sqrt_nonneg _)

/-- The threshold is the least natural number whose square reaches the scale. -/
theorem tailThreshold_le_iff (J k a : ℕ) : tailThreshold J k ≤ a ↔ tailScale J k ≤ a ^ 2 := by
  unfold tailThreshold
  rw [Nat.ceil_le, Real.sqrt_le_left (Nat.cast_nonneg a)]
  exact_mod_cast Iff.rfl

/-- At the terminal check `h_J = 2 √N` exactly. -/
theorem tailThreshold_terminal (J : ℕ) : tailThreshold J J = 2 ^ (J + 1) := by
  have hs : tailScale J J = (2 ^ (J + 1)) ^ 2 := by
    unfold tailScale
    rw [Nat.sub_self, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    ring
  apply le_antisymm
  · exact (tailThreshold_le_iff J J _).2 hs.le
  · have h := tailScale_le_threshold_sq J J
    rw [hs] at h
    have h' : (2 ^ (J + 1)) ^ 2 ≤ tailThreshold J J ^ 2 := by exact_mod_cast h
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h'

/-- The real form of a resolving check. -/
theorem tailResolvedAt_iff (J k : ℕ) (ω : ℕ → Bool) :
    tailResolvedAt J k ω ↔
      (tailThreshold J k : ℝ) / 4 ^ k < |prefixMean observations (4 ^ k) ω - 1 / 2| := by
  have hn : (0 : ℝ) < 4 ^ k := by positivity
  have he : prefixMean observations (4 ^ k) ω - 1 / 2 =
      (2 * (tailHeads (4 ^ k) ω : ℝ) - 4 ^ k) / (2 * 4 ^ k) := by
    rw [prefixMean_eq_heads]
    push_cast
    field_simp
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * 4 ^ k),
    div_lt_div_iff₀ hn (by positivity)]
  unfold tailResolvedAt
  rw [← @Int.cast_lt ℝ]
  push_cast
  constructor
  · intro h
    nlinarith [h]
  · intro h
    nlinarith [h]

theorem tailStop_le (J : ℕ) (ω : ℕ → Bool) : tailStop J ω ≤ J :=
  Nat.sInf_le (Or.inl le_rfl)

theorem tailStop_mem (J : ℕ) (ω : ℕ → Bool) :
    J ≤ tailStop J ω ∨ tailResolvedAt J (tailStop J ω) ω :=
  Nat.sInf_mem (s := {k | J ≤ k ∨ tailResolvedAt J k ω}) ⟨J, Or.inl le_rfl⟩

/-- Every check before the stopping check failed to resolve. -/
theorem not_resolved_of_lt_stop {J k : ℕ} {ω : ℕ → Bool} (h : k < tailStop J ω) :
    ¬ tailResolvedAt J k ω := fun hr =>
  Nat.notMem_of_lt_sInf h (Or.inr hr)

/-- The work is at least one flip and at most `N = 4^J` on every tape. -/
theorem tailWork_pos (J : ℕ) (ω : ℕ → Bool) : 1 ≤ tailWork J ω :=
  Nat.one_le_pow _ _ (by norm_num)

theorem tailWork_le (J : ℕ) (ω : ℕ → Bool) : tailWork J ω ≤ 4 ^ J :=
  Nat.pow_le_pow_right (by norm_num) (tailStop_le J ω)

/-- The coin is unresolved exactly when its stopping check does not resolve. -/
theorem tailUnresolved_iff (J : ℕ) (ω : ℕ → Bool) :
    tailUnresolved J ω ↔ ¬ tailResolvedAt J (tailStop J ω) ω := by
  constructor
  · intro h
    exact h _ (tailStop_le J ω)
  · intro hn k hk hr
    have hle : tailStop J ω ≤ k := Nat.sInf_le (Or.inr hr)
    rcases tailStop_mem J ω with hJ | hres
    · have : tailStop J ω = k := le_antisymm hle (hk.trans hJ)
      exact hn (this ▸ hr)
    · exact hn hres

/-- A resolving check reads only the first `4^k` flips. -/
theorem tailResolvedAt_congr {J k : ℕ} {ω ω' : ℕ → Bool} (h : ∀ i < 4 ^ k, ω i = ω' i) :
    tailResolvedAt J k ω ↔ tailResolvedAt J k ω' := by
  unfold tailResolvedAt
  rw [tailHeads_congr h]

/-- The stopping check is determined by the flips that were bought. -/
theorem tailStop_congr {J : ℕ} {ω ω' : ℕ → Bool} (h : ∀ i < tailWork J ω, ω i = ω' i) :
    tailStop J ω' = tailStop J ω := by
  have hk : ∀ k, k ≤ tailStop J ω → (tailResolvedAt J k ω ↔ tailResolvedAt J k ω') :=
    fun k hk => tailResolvedAt_congr fun i hi =>
      h i (hi.trans_le (Nat.pow_le_pow_right (by norm_num) hk))
  apply le_antisymm
  · apply Nat.sInf_le
    rcases tailStop_mem J ω with hJ | hres
    · exact Or.inl hJ
    · exact Or.inr ((hk _ le_rfl).1 hres)
  · have hle : tailStop J ω' ≤ tailStop J ω := by
      apply Nat.sInf_le
      rcases tailStop_mem J ω with hJ | hres
      · exact Or.inl hJ
      · exact Or.inr ((hk _ le_rfl).1 hres)
    apply Nat.sInf_le
    rcases tailStop_mem J ω' with hJ | hres
    · exact Or.inl hJ
    · exact Or.inr ((hk _ hle).2 hres)

theorem tailWork_congr {J : ℕ} {ω ω' : ℕ → Bool} (h : ∀ i < tailWork J ω, ω i = ω' i) :
    tailWork J ω' = tailWork J ω := by
  unfold tailWork
  rw [tailStop_congr h]

/-- The unresolved indicator is determined by the flips that were bought. -/
theorem tailUnresolved_congr {J : ℕ} {ω ω' : ℕ → Bool}
    (h : ∀ i < tailWork J ω, ω i = ω' i) : tailUnresolved J ω' ↔ tailUnresolved J ω := by
  rw [tailUnresolved_iff, tailUnresolved_iff, tailStop_congr h]
  exact not_congr (tailResolvedAt_congr h).symm

/-- Complementing every flip preserves each check. -/
theorem tailResolvedAt_flip (J k : ℕ) (ω : ℕ → Bool) :
    tailResolvedAt J k (tapeFlip ω) ↔ tailResolvedAt J k ω := by
  unfold tailResolvedAt
  rw [tailHeads_flip, Nat.cast_sub (tailHeads_le _ ω)]
  have he : 2 * (((4 ^ k : ℕ) : ℤ) - (tailHeads (4 ^ k) ω : ℤ)) - ((4 ^ k : ℕ) : ℤ) =
      -(2 * (tailHeads (4 ^ k) ω : ℤ) - ((4 ^ k : ℕ) : ℤ)) := by ring
  rw [he, abs_neg]

/-- Complementing every flip preserves the complete stopping path. -/
theorem tailStop_flip (J : ℕ) (ω : ℕ → Bool) : tailStop J (tapeFlip ω) = tailStop J ω := by
  unfold tailStop
  congr 1
  ext k
  exact or_congr Iff.rfl (tailResolvedAt_flip J k ω)

theorem tailWork_flip (J : ℕ) (ω : ℕ → Bool) : tailWork J (tapeFlip ω) = tailWork J ω := by
  unfold tailWork
  rw [tailStop_flip]

/-- Complementing every flip preserves the unresolved indicator. -/
theorem tailUnresolved_flip (J : ℕ) (ω : ℕ → Bool) :
    tailUnresolved J (tapeFlip ω) ↔ tailUnresolved J ω := by
  unfold tailUnresolved
  simp only [tailResolvedAt_flip]

/-- A function of finitely many flips is measurable. -/
theorem measurable_of_tape_prefix {α : Type*} [MeasurableSpace α] (M : ℕ)
    (f : (ℕ → Bool) → α) (h : ∀ ω ω', (∀ i < M, ω i = ω' i) → f ω = f ω') :
    Measurable f := by
  let ext : (Fin M → Bool) → ℕ → Bool := fun v i => if hi : i < M then v ⟨i, hi⟩ else false
  have he : f = (fun v => f (ext v)) ∘ tapePrefix M := by
    funext ω
    exact h ω _ fun i hi => by simp [ext, tapePrefix, hi]
  rw [he]
  exact (measurable_of_countable _).comp (measurable_prefix M)

theorem measurable_tailHeads (n : ℕ) : Measurable (tailHeads n) :=
  measurable_of_tape_prefix n _ fun _ _ h => tailHeads_congr h

theorem measurable_tailStop (J : ℕ) : Measurable (tailStop J) :=
  measurable_of_tape_prefix (4 ^ J) _ fun ω _ h =>
    (tailStop_congr fun i hi => h i (hi.trans_le (tailWork_le J ω))).symm

theorem measurable_tailWork (J : ℕ) : Measurable (tailWork J) :=
  measurable_of_tape_prefix (4 ^ J) _ fun ω _ h =>
    (tailWork_congr fun i hi => h i (hi.trans_le (tailWork_le J ω))).symm

theorem measurable_tapeFlip : Measurable tapeFlip :=
  Measurable.of_eval fun i =>
    (measurable_of_countable (fun b : Bool => !b)).comp (measurable_pi_apply i)

theorem measurableSet_tailResolvedAt (J k : ℕ) : MeasurableSet {ω | tailResolvedAt J k ω} :=
  measurable_tailHeads (4 ^ k) (MeasurableSet.of_discrete
    (s := {S : ℕ | 2 * (tailThreshold J k : ℤ) < |2 * (S : ℤ) - ((4 ^ k : ℕ) : ℤ)|}))

theorem measurableSet_tailUnresolved (J : ℕ) : MeasurableSet {ω | tailUnresolved J ω} := by
  have h : {ω | tailUnresolved J ω} =
      ⋂ k ∈ Finset.range (J + 1), {ω | tailResolvedAt J k ω}ᶜ := by
    ext ω
    simp [tailUnresolved]
  rw [h]
  exact Finset.measurableSet_biInter _ fun k _ => (measurableSet_tailResolvedAt J k).compl

end ThresholdHC.ArbitraryLawAdaptation
