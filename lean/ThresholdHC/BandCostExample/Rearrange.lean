import ThresholdHC.BandCostExample.Objective

/-! Rearrangement bounds for the dyadic gaps: `k` distinct gaps `2^{-(n+1)}`
sum to at most `1 - 2^{-k}`, the sum of the `k` largest; two distinct gaps other
than `1/2, 1/4` sum to at most `5/8`. -/
noncomputable section
open scoped ENNReal
namespace ThresholdHC.BandCostExample

/-- `k` distinct dyadic gaps sum to at most the sum of the `k` largest. -/
theorem half_sum_le (S : Finset ℕ) : ∑ n ∈ S, (1/2 : ℝ)^(n+1) ≤ 1 - (1/2 : ℝ)^S.card := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hlt ih =>
    have ha : a ∉ S := fun h => lt_irrefl a (hlt a h)
    have hcard : S.card ≤ a := by
      have h := Finset.card_le_card (show S ⊆ Finset.range a from
        fun x hx => Finset.mem_range.mpr (hlt x hx))
      rwa [Finset.card_range] at h
    have hp : (1/2 : ℝ)^(a+1) ≤ (1/2 : ℝ)^(S.card+1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have h2 : (1/2 : ℝ)^(S.card+1) = (1/2 : ℝ)^S.card / 2 := by
      rw [pow_succ]
      ring
    linarith

/-- Two distinct dyadic gaps other than `1/2, 1/4` sum to at most `5/8`. -/
theorem pair_sum_le (S : Finset ℕ) (hc : S.card = 2) (hS : S ≠ {0, 1}) :
    ∑ n ∈ S, (1/2 : ℝ)^(n+1) ≤ 5/8 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc
  rw [Finset.sum_pair hab]
  have key : ∀ x y : ℕ, x < y → ¬ (x = 0 ∧ y = 1) →
      (1/2 : ℝ)^(x+1) + (1/2 : ℝ)^(y+1) ≤ 5/8 := by
    intro x y hxy hne
    have hy : 2 ≤ y := by omega
    have h1 : (1/2 : ℝ)^(x+1) ≤ (1/2 : ℝ)^1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h2 : (1/2 : ℝ)^(y+1) ≤ (1/2 : ℝ)^3 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    norm_num at h1 h2
    linarith
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h (by rintro ⟨rfl, rfl⟩; exact hS rfl)
  · rw [add_comm]
    exact key b a h (by rintro ⟨rfl, rfl⟩; exact hS (Finset.pair_comm 1 0))

theorem X_eq (s : Fin 64 → Bool) :
    X s = ∑ n ∈ (chosen s).map Fin.valEmbedding, (1/2 : ℝ)^(n+1) := by
  rw [X, Finset.sum_map]
  rfl

/-- The retained gaps sum to at most `1 - 2^{-k}`. -/
theorem X_le (s : Fin 64 → Bool) : X s ≤ 1 - (1/2 : ℝ)^(kc s) := by
  rw [X_eq, kc, ← Finset.card_map Fin.valEmbedding]
  exact half_sum_le _

/-- Two retained gaps other than the two largest sum to at most `5/8`. -/
theorem X_pair (s : Fin 64 → Bool) (hk : kc s = 2) (hs : s ≠ topTwo) : X s ≤ 5/8 := by
  rw [X_eq]
  apply pair_sum_le
  · rw [Finset.card_map]
    exact hk
  · intro he
    apply hs
    funext i
    rw [Bool.eq_iff_iff]
    have hm : s i = true ↔ i.val ∈ (chosen s).map Fin.valEmbedding := by
      rw [Finset.mem_map]
      constructor
      · intro h
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
      · rintro ⟨j, hj, hji⟩
        have : j = i := Fin.ext hji
        subst this
        exact (Finset.mem_filter.mp hj).2
    rw [hm, he]
    simp only [Finset.mem_insert, Finset.mem_singleton, topTwo, decide_eq_true_eq]
    omega

/-- All 64 gaps sum to at most `1`. -/
theorem atoms_sum_le : ∑ i, (atoms i : ℝ) ≤ 1 := by
  have h := X_le (fun _ => true)
  have hX : X (fun _ => true) = ∑ i, (atoms i : ℝ) := by
    rw [X, chosen]
    congr 1
  have hp : (0:ℝ) ≤ (1/2)^(kc fun _ => true) := by positivity
  linarith

end ThresholdHC.BandCostExample
