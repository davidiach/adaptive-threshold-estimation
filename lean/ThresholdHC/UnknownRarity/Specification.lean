import ThresholdHC.Tier6.AlgorithmModel
import ThresholdHC.StoppingProgram.PositiveValue

/-! Target statements for the obstruction to completely uniform adaptation to
unknown rarity: `docs/process/TRACK_D.md`, section An obstruction to
completely uniform adaptation to unknown rarity (restated in
`docs/SECONDARY_CLAIMS.md` and `docs/RESULTS.md`).

The source fixes a known gap `0 < d < 1/2` and a family of estimators `A_B`,
indexed by the budget, that does not receive the rarity bound `ρ`. Each `A_B`
stops almost surely for every constant positive-sign prior `θ ∈ [0,1/4]`. No
universal finite `C` makes the root-mean-square error at most
`C min(ρ, √ρ/(d√B))` for every budget, every `ρ ∈ (0,1/4]` and every `θ ≤ ρ`.

The model is the Tier 6 adaptive experiment with gap law `Measure.dirac d`:
every fresh coin has gap `d`, the seed space is an arbitrary measurable space
(all algorithmic randomness), and the policy may interleave observations and
create coins adaptively. Quantifier order encodes that the family does not
receive `ρ`. The RMS error is the extended-real `rootMeanRisk`, which keeps
infinite risk. The target `θ` equals `signMean (dirac d) (constantPrior θ _)`
by `StoppingProgram.constantPrior_mean`. The budget index is real (`B ≥ 1`);
`FixedBudgetObstructionStatement` is index-free and goes beyond the source:
one estimator, one budget `B > 4C²/d²`, and stopping only at `θ = 1/4`.
`ExpectedWorkObstructionStatement` is the source remark that expected-work
bounds imply the stopping premise. `StoppedTranscriptACStatement` is the
stopped-transcript absolute continuity of the proof, in the direction used. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.UnknownRarity
open ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.StoppingProgram (constantPrior)

/-- The source claim: a budget-indexed family that does not receive `ρ`, stopping
almost surely at every constant prior in `[0,1/4]`, has no single finite `C`
with RMS error at most `C min(ρ, √ρ/(d√B))` for all `B ≥ 1`, `ρ ∈ (0,1/4]` and
`θ ∈ [0,ρ]`. -/
def UnknownRarityObstructionStatement : Prop :=
  ∀ (d : Gap), (d : ℝ) < 1/2 →
  ∀ (C : ℝ) (R : ℝ → Type) [∀ B, MeasurableSpace (R B)] (A : ∀ B, AdaptiveEstimator (R B)),
    (∀ B : ℝ, 1 ≤ B → ∀ (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1), θ ≤ 1/4 →
      ∀ᵐ z ∂experimentLaw (Measure.dirac d) (A B) (constantPrior θ hθ),
        ∃ n, (A B).policy z.1.1 (processHistory z.2 n) = none) →
    ¬ ∀ B : ℝ, 1 ≤ B → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1/4 →
      ∀ (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1), θ ≤ ρ →
        rootMeanRisk (experimentLaw (Measure.dirac d) (A B) (constantPrior θ hθ))
            (populationOutput (A B)) θ ≤
          ENNReal.ofReal (C * min ρ (Real.sqrt ρ / ((d : ℝ) * Real.sqrt B)))

/-- Strengthening beyond the source: one estimator, one budget `B > 4C²/d²`, and
stopping only at `θ = 1/4`. -/
def FixedBudgetObstructionStatement : Prop :=
  ∀ (d : Gap), (d : ℝ) < 1/2 → ∀ (C B : ℝ), 4 * C^2 / (d : ℝ)^2 < B →
  ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R),
    (∀ᵐ z ∂experimentLaw (Measure.dirac d) A (constantPrior (1/4) (by norm_num)),
        ∃ n, A.policy z.1.1 (processHistory z.2 n) = none) →
    ¬ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1/4 → ∀ (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1), θ ≤ ρ →
        rootMeanRisk (experimentLaw (Measure.dirac d) A (constantPrior θ hθ))
            (populationOutput A) θ ≤
          ENNReal.ofReal (C * min ρ (Real.sqrt ρ / ((d : ℝ) * Real.sqrt B)))

/-- Source remark: finite expected work at every constant prior in `[0,1/4]`
implies the stopping premise, so it gives the same obstruction. -/
def ExpectedWorkObstructionStatement : Prop :=
  ∀ (d : Gap), (d : ℝ) < 1/2 →
  ∀ (C : ℝ) (R : ℝ → Type) [∀ B, MeasurableSpace (R B)] (A : ∀ B, AdaptiveEstimator (R B)),
    (∀ B : ℝ, 1 ≤ B → ∀ (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1), θ ≤ 1/4 →
      expectedWork (Measure.dirac d) (A B) (constantPrior θ hθ) < ∞) →
    ¬ ∀ B : ℝ, 1 ≤ B → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1/4 →
      ∀ (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1), θ ≤ ρ →
        rootMeanRisk (experimentLaw (Measure.dirac d) (A B) (constantPrior θ hθ))
            (populationOutput (A B)) θ ≤
          ENNReal.ofReal (C * min ρ (Real.sqrt ρ / ((d : ℝ) * Real.sqrt B)))

/-- The stopped-transcript absolute continuity of the source proof, in the
direction the proof uses: at a point-mass gap `d < 1/2`, the law of the seed and
tape under a sign law `v` at which the estimator stops almost surely is
absolutely continuous with respect to its law under any sign law `q`. -/
def StoppedTranscriptACStatement : Prop :=
  ∀ (d : Gap), (d : ℝ) < 1/2 →
  ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R) (q v : SignLaw),
    (∀ᵐ z ∂experimentLaw (Measure.dirac d) A v,
        ∃ n, A.policy z.1.1 (processHistory z.2 n) = none) →
    (experimentLaw (Measure.dirac d) A v).map (fun z => (z.1.1, z.2)) ≪
      (experimentLaw (Measure.dirac d) A q).map (fun z => (z.1.1, z.2))

end ThresholdHC.UnknownRarity
