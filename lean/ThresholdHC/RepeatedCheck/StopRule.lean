import ThresholdHC.RepeatedCheck.Exact

/-! The observable stop rule of display (29) of
`research/2026-10-30-confidence-transfer/ANYTIME.md`: stop at the first time
`n ≤ N` at which the fixed-time interval excludes the reference value `1/4`
(the check `(4H_n - n)² > 12n` fires), or at time `N`.

`stopTime N` is that rule. It is a stopping time of the flips
(`stopTime_observable`: whether it equals `n` depends on the first `n` flips
only), the interval reported at the stopped time misses `1/4` exactly on the
repeated-check event (`stopped_miss_iff`), and at `θ = 1/4`, `N = 512` this
stopped miss has probability `1 - survivorTotal / 4^512 > 1/4`
(`stopped_check`), although every fixed-time miss has probability at most
`1/4`. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open ThresholdHC.Tier2

namespace ThresholdHC.RepeatedCheck

/-- Heads among the first `n` flips. -/
def headCount (n : ℕ) (ω : ℕ → Bool) : ℕ := ((Finset.range n).filter (fun t => ω t = true)).card

theorem stopTime_exists (N : ℕ) (ω : ℕ → Bool) :
    ∃ n, n = N ∨ crossNat n (headCount n ω) = true :=
  ⟨N, Or.inl rfl⟩

/-- The stop rule: the first `n` at which the check fires, or `N`. -/
def stopTime (N : ℕ) (ω : ℕ → Bool) : ℕ := Nat.find (stopTime_exists N ω)

theorem stopTime_le (N : ℕ) (ω : ℕ → Bool) : stopTime N ω ≤ N :=
  Nat.find_min' (stopTime_exists N ω) (Or.inl rfl)

theorem headCount_congr (n : ℕ) (ω ω' : ℕ → Bool) (h : ∀ t < n, ω t = ω' t) (m : ℕ)
    (hm : m ≤ n) : headCount m ω = headCount m ω' := by
  unfold headCount
  congr 1
  apply Finset.filter_congr
  intro t ht
  rw [h t (lt_of_lt_of_le (Finset.mem_range.mp ht) hm)]

/-- The stop rule is observable: if two flip sequences agree on their first
`n` flips, they stop at time `n` together. -/
theorem stopTime_observable (N n : ℕ) (ω ω' : ℕ → Bool) (h : ∀ t < n, ω t = ω' t)
    (hs : stopTime N ω = n) : stopTime N ω' = n := by
  unfold stopTime at hs ⊢
  rw [Nat.find_eq_iff] at hs ⊢
  obtain ⟨h1, h2⟩ := hs
  refine ⟨?_, fun m hm => ?_⟩
  · rw [← headCount_congr n ω ω' h n le_rfl]
    exact h1
  · rw [← headCount_congr n ω ω' h m hm.le]
    exact h2 m hm

/-- The interval reported at the stopped time misses `1/4` exactly when the
check fires at some `n ≤ N`. -/
theorem stopped_miss_iff (N : ℕ) (ω : ℕ → Bool) :
    12 * (stopTime N ω : ℝ) < (4 * (headCount (stopTime N ω) ω : ℝ) - stopTime N ω) ^ 2 ↔
      ω ∈ repeatedEvent N := by
  constructor
  · intro h
    exact ⟨stopTime N ω, stopTime_le N ω, h⟩
  · rintro ⟨n, hn, hc⟩
    have hcn : crossNat n (headCount n ω) = true := (crossNat_iff _ _).mpr hc
    have hle : stopTime N ω ≤ n := Nat.find_min' (stopTime_exists N ω) (Or.inr hcn)
    have hspec := Nat.find_spec (stopTime_exists N ω)
    change stopTime N ω = N ∨ crossNat (stopTime N ω) (headCount (stopTime N ω) ω) = true at hspec
    rcases hspec with hs | hs
    · have hsn : stopTime N ω = n := by
        have := stopTime_le N ω
        omega
      rw [hsn]
      exact hc
    · exact (crossNat_iff _ _).mp hs

/-- At `θ = 1/4`, the interval reported at the stopped time of the rule with
horizon `512` misses `1/4` with probability `1 - survivorTotal / 4^512`. -/
theorem stopped_check_exact (θ : unitInterval) (hθ : (θ : ℝ) = 1/4) :
    (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false θ)).real
        {ω | 12 * (stopTime 512 ω : ℝ) <
          (4 * (headCount (stopTime 512 ω) ω : ℝ) - stopTime 512 ω) ^ 2} =
      1 - (survivorTotal : ℝ) / 4 ^ 512 := by
  have he : {ω : ℕ → Bool | 12 * (stopTime 512 ω : ℝ) <
      (4 * (headCount (stopTime 512 ω) ω : ℝ) - stopTime 512 ω) ^ 2} = repeatedEvent 512 := by
    ext ω
    exact stopped_miss_iff 512 ω
  rw [he]
  exact repeated_check_exact θ hθ

/-- The stopped interval fails with probability more than `1/4`. -/
theorem stopped_check (θ : unitInterval) (hθ : (θ : ℝ) = 1/4) :
    1/4 < (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false θ)).real
        {ω | 12 * (stopTime 512 ω : ℝ) <
          (4 * (headCount (stopTime 512 ω) ω : ℝ) - stopTime 512 ω) ^ 2} := by
  rw [stopped_check_exact θ hθ]
  exact lt_trans (by norm_num) survivorTotal_lower

end ThresholdHC.RepeatedCheck
