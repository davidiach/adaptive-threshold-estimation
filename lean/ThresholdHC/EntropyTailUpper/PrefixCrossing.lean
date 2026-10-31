import ThresholdHC.CriticalEntropy.SequentialModel

/-! A countable-time likelihood crossing bound proved on actual observed
prefixes. It needs neither termination nor an iid assumption on the null law,
so it applies to the full all-negative mixture in the reference bank. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ThresholdHC.EntropyTailUpper
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy

def firstPrefixHit (hit : (n : ℕ) → (Fin n → Bool) → Prop) (n : ℕ) : Set (ℕ → Bool) :=
  {ω | hit n (tapePrefix n ω) ∧ ∀ k < n, ¬ hit k (tapePrefix k ω)}

def everPrefixHit (hit : (n : ℕ) → (Fin n → Bool) → Prop) : Set (ℕ → Bool) :=
  {ω | ∃ n, hit n (tapePrefix n ω)}

theorem firstPrefixHit_ext (hit : (n : ℕ) → (Fin n → Bool) → Prop) (n : ℕ)
    (ω ω' : ℕ → Bool) (he : tapePrefix n ω = tapePrefix n ω') :
    ω ∈ firstPrefixHit hit n ↔ ω' ∈ firstPrefixHit hit n := by
  have hk (k : ℕ) (hkn : k < n) : tapePrefix k ω = tapePrefix k ω' :=
    prefix_eq_restrict he hkn.le
  simp only [firstPrefixHit, mem_ofPred_eq, he]
  congr! 2 with k
  exact forall_congr' (fun hkn => by rw [hk k hkn])

theorem firstPrefixHit_eq_preimage (hit : (n : ℕ) → (Fin n → Bool) → Prop) (n : ℕ) :
    firstPrefixHit hit n = tapePrefix n ⁻¹'
      {w | completePrefix n w ∈ firstPrefixHit hit n} := by
  ext ω
  exact firstPrefixHit_ext hit n ω (completePrefix n (tapePrefix n ω))
    (tapePrefix_completePrefix n _).symm

theorem measurableSet_firstPrefixHit (hit : (n : ℕ) → (Fin n → Bool) → Prop) (n : ℕ) :
    MeasurableSet (firstPrefixHit hit n) := by
  rw [firstPrefixHit_eq_preimage]
  exact (Set.to_countable _).measurableSet.preimage (measurable_prefix n)

theorem firstPrefixHit_disjoint (hit : (n : ℕ) → (Fin n → Bool) → Prop) :
    Pairwise (fun i j => Disjoint (firstPrefixHit hit i) (firstPrefixHit hit j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro ω hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · exact hj.2 i h hi.1
  · exact hi.2 j h hj.1

theorem everPrefixHit_eq_iUnion (hit : (n : ℕ) → (Fin n → Bool) → Prop) :
    everPrefixHit hit = ⋃ n, firstPrefixHit hit n := by
  classical
  ext ω
  constructor
  · intro h
    exact mem_iUnion.mpr ⟨Nat.find h, Nat.find_spec h, fun k hk => Nat.find_min h hk⟩
  · intro h
    obtain ⟨n, hn⟩ := mem_iUnion.mp h
    exact ⟨n, hn.1⟩

theorem measure_firstPrefixHit_le (hit : (n : ℕ) → (Fin n → Bool) → Prop)
    (P Q : Measure (ℕ → Bool)) (c : ℝ≥0∞)
    (hcross : ∀ n w, hit n w → P (tapePrefix n ⁻¹' {w}) ≤ c * Q (tapePrefix n ⁻¹' {w}))
    (n : ℕ) : P (firstPrefixHit hit n) ≤ c * Q (firstPrefixHit hit n) := by
  classical
  let S : Finset (Fin n → Bool) := Finset.univ.filter (fun w => completePrefix n w ∈ firstPrefixHit hit n)
  have he : firstPrefixHit hit n = tapePrefix n ⁻¹' (S : Set (Fin n → Bool)) := by
    rw [firstPrefixHit_eq_preimage]
    congr 1
    ext w
    simp [S]
  have hm (w : Fin n → Bool) (_ : w ∈ S) : MeasurableSet (tapePrefix n ⁻¹' {w}) :=
    (measurableSet_singleton w).preimage (measurable_prefix n)
  rw [he, ← sum_measure_preimage_singleton S hm, ← sum_measure_preimage_singleton S hm,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w hw
  apply hcross n w
  have hmem : completePrefix n w ∈ firstPrefixHit hit n := (Finset.mem_filter.mp hw).2
  simpa only [tapePrefix_completePrefix] using hmem.1

theorem measure_everPrefixHit_le (hit : (n : ℕ) → (Fin n → Bool) → Prop)
    (P Q : Measure (ℕ → Bool)) [IsProbabilityMeasure Q] (c : ℝ≥0∞)
    (hcross : ∀ n w, hit n w → P (tapePrefix n ⁻¹' {w}) ≤ c * Q (tapePrefix n ⁻¹' {w})) :
    P (everPrefixHit hit) ≤ c := by
  rw [everPrefixHit_eq_iUnion, measure_iUnion (firstPrefixHit_disjoint hit)
    (measurableSet_firstPrefixHit hit)]
  calc
    _ ≤ ∑' n, c * Q (firstPrefixHit hit n) :=
      ENNReal.tsum_le_tsum (measure_firstPrefixHit_le hit P Q c hcross)
    _ = c * ∑' n, Q (firstPrefixHit hit n) := ENNReal.tsum_mul_left
    _ = c * Q (⋃ n, firstPrefixHit hit n) := by
      rw [measure_iUnion (firstPrefixHit_disjoint hit) (measurableSet_firstPrefixHit hit)]
    _ ≤ c * 1 := mul_le_mul_right prob_le_one c
    _ = c := mul_one c

end ThresholdHC.EntropyTailUpper
