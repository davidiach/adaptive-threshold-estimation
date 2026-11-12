import ThresholdHC.EntropyTailAssembly.ErrorCaps
import ThresholdHC.EntropyTailAssembly.AccuracySchedule

/-! The cap search of a plan.

The planner is given an error envelope `e`, an upper bound of the resolved
error `η(M)` at every cap `M`. Starting from the cap `4`, at each level it
multiplies the cap by four until `e(M) ≤ δ_l/8`, and carries the cap to the
next level. The search stops exactly when the envelope gets below every
positive level along the powers of four, which is its termination
requirement. The caps it returns are admissible for the true resolved error,
they are at least `4`, and they do not decrease with the level. The exact
resolved error of a finite measure satisfies the requirement. -/

noncomputable section
open MeasureTheory Filter Topology
namespace ThresholdHC.KnownLawPlanner
open ThresholdHC.Tier6 ThresholdHC.EntropyTailAssembly

/-- The termination requirement of the cap search: beyond every exponent the
envelope gets below every positive level. -/
def EnvelopeVanishes (e : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ k₀ : ℕ, ∃ k : ℕ, k₀ ≤ k ∧ e (4 ^ k) ≤ ε

/-- One search: the least exponent `k ≥ k₀` with `e(4^k) ≤ ε`. -/
def searchCap (e : ℝ → ℝ) (he : EnvelopeVanishes e) (ε : ℝ) (hε : 0 < ε) (k₀ : ℕ) : ℕ :=
  Nat.find (he ε hε k₀)

theorem searchCap_spec (e : ℝ → ℝ) (he : EnvelopeVanishes e) (ε : ℝ) (hε : 0 < ε) (k₀ : ℕ) :
    k₀ ≤ searchCap e he ε hε k₀ ∧ e (4 ^ searchCap e he ε hε k₀) ≤ ε :=
  Nat.find_spec (he ε hε k₀)

/-- The search stops at the first admissible cap: every earlier cap from
`4^k₀` on fails the test. -/
theorem searchCap_min (e : ℝ → ℝ) (he : EnvelopeVanishes e) (ε : ℝ) (hε : 0 < ε) (k₀ : ℕ)
    {k : ℕ} (hk₀ : k₀ ≤ k) (hk : k < searchCap e he ε hε k₀) : ε < e (4 ^ k) := by
  have h := Nat.find_min (he ε hε k₀) hk
  exact lt_of_not_ge fun hle => h ⟨hk₀, hle⟩

/-- The cap exponents of the plan. Level zero starts from the cap `4`, and
each later level starts from the cap of the level before. -/
def searchCaps (e : ℝ → ℝ) (he : EnvelopeVanishes e) {ρ : ℝ} (hρ : 0 < ρ) : ℕ → ℕ
  | 0 => searchCap e he (levelAccuracy ρ 0/8) (div_pos (levelAccuracy_pos hρ 0) (by norm_num)) 1
  | l+1 => searchCap e he (levelAccuracy ρ (l+1)/8)
      (div_pos (levelAccuracy_pos hρ (l+1)) (by norm_num)) (searchCaps e he hρ l)

/-- Every cap of the plan passes the test of its level. -/
theorem searchCaps_spec (e : ℝ → ℝ) (he : EnvelopeVanishes e) {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ) :
    e (4 ^ searchCaps e he hρ l) ≤ levelAccuracy ρ l/8 := by
  cases l with
  | zero => exact (searchCap_spec e he _ _ 1).2
  | succ l => exact (searchCap_spec e he _ _ _).2

theorem searchCaps_succ_ge (e : ℝ → ℝ) (he : EnvelopeVanishes e) {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ) :
    searchCaps e he hρ l ≤ searchCaps e he hρ (l+1) :=
  (searchCap_spec e he _ _ _).1

/-- The caps do not decrease with the level. -/
theorem searchCaps_monotone (e : ℝ → ℝ) (he : EnvelopeVanishes e) {ρ : ℝ} (hρ : 0 < ρ) :
    Monotone (searchCaps e he hρ) :=
  monotone_nat_of_le_succ (searchCaps_succ_ge e he hρ)

/-- Every cap is at least `4`. -/
theorem one_le_searchCaps (e : ℝ → ℝ) (he : EnvelopeVanishes e) {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ) :
    1 ≤ searchCaps e he hρ l :=
  le_trans (searchCap_spec e he _ _ 1).1 (searchCaps_monotone e he hρ (Nat.zero_le l))

/-- The caps are admissible for the true resolved error, when the envelope
bounds it. -/
theorem searchCaps_admissible (ν : Measure Gap) (e : ℝ → ℝ) (he : EnvelopeVanishes e)
    (hbound : ∀ M : ℝ, eta ν M ≤ e M) {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ) :
    eta ν (4 ^ searchCaps e he hρ l) ≤ levelAccuracy ρ l/8 :=
  (hbound _).trans (searchCaps_spec e he hρ l)

/-- The exact resolved error of a finite measure meets the termination
requirement. -/
theorem eta_vanishes (ν : Measure Gap) [IsFiniteMeasure ν] : EnvelopeVanishes (eta ν) := by
  intro ε hε k₀
  have h := (eta_tendsto ν).eventually (gt_mem_nhds hε)
  obtain ⟨k, hk, hlt⟩ := (eventually_ge_atTop k₀ |>.and h).exists
  exact ⟨k, hk, hlt.le⟩

end ThresholdHC.KnownLawPlanner
