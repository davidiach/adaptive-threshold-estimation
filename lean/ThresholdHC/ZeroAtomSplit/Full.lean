import ThresholdHC.ZeroAtomSplit.Support

/-! The zero-atom split of the selection functional,
`K_α = min{ρ, z + (1 - z) K_{η,ρ/(1-z)}}` for `α = z δ₀ + (1 - z) η`, and its
form for an arbitrary probability law on `[0, 1/2]` with `α{0} < 1`. -/
noncomputable section
namespace ThresholdHC.ZeroAtomSplit
open MeasureTheory ThresholdHC.ArbitraryLawAdaptation

/-- The zero-atom split `K_{zδ₀+(1-z)η,ρ} = min{ρ, z + (1 - z) K_{η,ρ/(1-z)}}`. -/
theorem zero_atom_split : ZeroAtomSplitStatement := by
  intro η _ z ρ B _ hz1 hρ hB
  exact zeroSelection_zeroAtomLaw η hz1 hρ hB

/-- The zero-atom split for a probability law on `[0, 1/2]` with `α{0} < 1`,
with `z = α{0}` and `η` the normalized positive part. -/
theorem zero_atom_split_law : ZeroAtomSplitLawStatement := by
  intro α _ ρ B hsupp hz hρ hB
  obtain ⟨hprob, hdec⟩ := zeroAtomLaw_decomposition α hsupp hz
  have h := zero_atom_split (positiveLaw α) (zeroMass α) ρ B measureReal_nonneg hz hρ hB
  rwa [hdec] at h

end ThresholdHC.ZeroAtomSplit
