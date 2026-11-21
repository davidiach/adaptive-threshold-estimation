import ThresholdHC.SmoothDensity.LatentLaw

/-! Target statements for the population class and the `G`-form of the target.
Sources: `paper/v6/core.tex`, section `sec:model`: equation `eq:model`
(`D ~ μ`, `S | D = d ~ Ber(q(d))`, `P = 1/2 + (2S - 1) D`), the population-class
sentence after it (`𝒢(μ) = {G_{μ,q} : q measurable}`) and the endpoint
sentence (`D = 0` excluded); `paper/v6/introduction.tex`, equations `eq:target`
(`θ(G) = P_G(P > 1/2)`) and `eq:modulus-intro` (`μ = L(|P - 1/2|)`);
`docs/MODEL_FIDELITY.md`, reviewer question 5, which asks for the converse
that every `G` with `|P - 1/2| ~ μ` is some `G_{μ,q}`.

Here `G_{μ,q}` is `SmoothDensity.latentLaw μ q`, the parameter law of the
independent-tape construction. The magnitude law `|P - 1/2| ~ μ` is read on
`ℝ`: the law of `|P - 1/2|` under `G` equals the law of the gap under `μ`,
viewed as a law on `ℝ`. This condition already excludes an atom at `P = 1/2`,
since every gap is positive.

* `LatentMagnitudeStatement`: every `G_{μ,q}` has magnitude law `μ`.
* `DisintegrationStatement`: every law of `P` with no atom at `1/2` is
  `G_{μ,q}` for its own magnitude law, written with `gapOf`.
* `PopulationClassStatement`: `𝒢(μ)` is exactly the set of laws of `P` on
  `[0,1]` with `|P - 1/2| ~ μ`.
* `GFormTargetStatement`: every such `G` is some `G_{μ,q}`, and every sign law
  `q` representing `G` has `θ = ∫ q dμ = P_G(P > 1/2)`.

The paper gives no written proof of the converse. The proofs are in
`Magnitude.lean`, `Disintegration.lean` and `Full.lean`. -/
noncomputable section
namespace ThresholdHC.LatentDisintegration
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.SmoothDensity

/-- The magnitude `|P - 1/2|` as a gap. The point `P = 1/2`, which has no gap,
goes to the default `1/2`; `DisintegrationStatement` assumes it is null. -/
def gapOf (p : unitInterval) : Gap :=
  ⟨if (p : ℝ) = 1/2 then 1/2 else |(p : ℝ) - 1/2|, by
    split_ifs with h
    · norm_num
    · exact ⟨abs_pos.2 (sub_ne_zero.2 h),
        abs_sub_le_iff.2 ⟨by linarith [p.2.2], by linarith [p.2.1]⟩⟩⟩

/-- Every `G_{μ,q}` has magnitude law `μ`: `|P - 1/2| ~ μ`, read on `ℝ`. -/
def LatentMagnitudeStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (latentLaw μ q).map (fun p : unitInterval => |(p : ℝ) - 1/2|) = μ.map Subtype.val

/-- The converse: a law of `P` with no atom at `1/2` is `G_{μ,q}` for its
magnitude law `μ = L(gapOf P)`. -/
def DisintegrationStatement : Prop :=
  ∀ (G : Measure unitInterval) [IsProbabilityMeasure G],
    G {p : unitInterval | (p : ℝ) = 1/2} = 0 → ∃ q : SignLaw, latentLaw (G.map gapOf) q = G

/-- `𝒢(μ)` is the set of all laws `G` of `P` on `[0,1]` with `|P - 1/2| ~ μ`. -/
def PopulationClassStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (G : Measure unitInterval),
    (∃ q : SignLaw, latentLaw μ q = G) ↔
      G.map (fun p : unitInterval => |(p : ℝ) - 1/2|) = μ.map Subtype.val

/-- The `G`-form of the target: every `G` with `|P - 1/2| ~ μ` is some
`G_{μ,q}`, and every such `q` has `θ = ∫ q dμ = P_G(P > 1/2)`. -/
def GFormTargetStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (G : Measure unitInterval),
    G.map (fun p : unitInterval => |(p : ℝ) - 1/2|) = μ.map Subtype.val →
      (∃ q : SignLaw, latentLaw μ q = G) ∧
      ∀ q : SignLaw, latentLaw μ q = G →
        signMean μ q.val = G.real {p : unitInterval | (1/2 : ℝ) < p}

end ThresholdHC.LatentDisintegration
