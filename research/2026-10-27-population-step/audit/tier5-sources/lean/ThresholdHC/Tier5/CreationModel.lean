import ThresholdHC.Tier4.Model

noncomputable section
namespace ThresholdHC.Tier5
open ThresholdHC.Tier3

/-- Restrict a countably indexed policy to a finite coin family. -/
def capPolicy (m : ℕ) (pol : List Bool → Option ℕ) (xs : List Bool) : Option (Fin m) :=
  (pol xs).bind (fun i => if hi : i < m then some ⟨i, hi⟩ else none)

/-- A cap containing every label queried anywhere in the finite decision tree.
This bound depends on the policy and horizon; there is no uniform coin cap. -/
def coinCap (n : ℕ) (pol : List Bool → Option ℕ) : ℕ :=
  (Finset.univ : Finset ((Fin n → Option Bool) × Fin n)).sup
    (fun wt => (pol (histBefore wt.1 wt.2)).getD 0) + 1

/-- The exact finite-prefix law of the unrestricted countable-coin policy. -/
def creationLaw {n : ℕ} (pol : List Bool → Option ℕ) (d q : ℕ → ℝ)
    (w : Prefix n) : ℝ :=
  transcriptLaw (capPolicy (coinCap n pol) pol)
    (fun i => d i.val) (fun i => q i.val) w

end ThresholdHC.Tier5
