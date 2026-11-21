import ThresholdHC.SmoothDensity.LatentLaw

/-! Target statement for the threshold form of the target
(`docs/MODEL_FIDELITY.md`; v6 `introduction.tex` writes
`θ(G) = P_G(P > 1/2)`).

A coin with gap `d` has success probability `P = 1/2 + d` with probability
`q(d)` (positive sign) and `P = 1/2 - d` otherwise.
For every gap law `μ` and sign law `q`, the target `θ = ∫ q dμ` is the
probability that `P > 1/2` under the latent parameter law `G_{μ,q}` of the
independent-tape construction. Lean had this only for laws with a density
(`SmoothDensity.represents_threshold_mean`). The proof is in `Threshold.lean`. -/
noncomputable section
namespace ThresholdHC.LatentThreshold
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.SmoothDensity

/-- `θ = G_{μ,q}(P > 1/2)` for every gap law and every sign law. -/
def ThresholdMeanStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    signMean μ q.val = (latentLaw μ q).real {p : unitInterval | (1/2 : ℝ) < p}

end ThresholdHC.LatentThreshold
