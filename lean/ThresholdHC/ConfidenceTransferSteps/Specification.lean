import ThresholdHC.ConfidenceProgram.Upper
import ThresholdHC.HardBudget.Specification
import ThresholdHC.Confidence.Model

/-! Target statements for the residual steps of the confidence-transfer note
`research/2026-10-30-confidence-transfer/NOTE.md` (Round 2, 30 October 2026).

* Equation (17) of the note, in the section on the general-law lower route:
  evaluating Proposition `prop:psi-null` (the note's (16)) at `h = √(ℓ/B)` with
  `b = Ψ(h)/64` and `J = (15Ψ(h)/16)²/(192h²)` in the note's Theorem 3 gives
  `r^exp(B,δ) ≥ Ψ(√(ℓ/B))/8192`, where `ℓ = log(1/δ)`. Here `Ψ` is `rarePsi μ ρ`,
  `√(ℓ/B)` is `ThresholdHC.Confidence.confidenceScale B δ`, and `r^exp` is
  `ThresholdHC.ConfidenceTransfer.rareConfidenceRadius`. The bound holds for every
  probability law of gaps (`PsiConfidenceNullStatement`).
* Equation (22) of the note, in the section Above the quadratic boundary and the
  fixed-gap anchor: for an exact power law `F(d) = (d/a)^α` on `(0,a]` with fixed
  `α > 2`, `r(B,δ) ≍_α min{ρ, √(ρ log(1/δ))/(a√B)}` under either budget
  convention. The exact law is `ExactPowerLaw μ α a`, an identity for the actual
  distribution function with no density assumed. Either convention is expressed
  by the chain `z/8192 ≤ r^exp ≤ r^hard ≤ C z`, where `r^hard` is
  `ThresholdHC.ConfidenceProgram.hardConfidenceRadius`, the radius under a cap of
  `⌊B⌋` flips on every valid observable path (`AboveTwoConfidenceStatement`).
  The lower constant `1/8192` is universal; the upper constant `C` depends only
  on `α`, as the note's `≍_α` allows.
* The remark after (22) (NOTE.md, the paragraph following the boxed display):
  the power-envelope RMS upper constructions are amplified without knowledge of
  the exact law. `AboveTwoConfidenceFamilyStatement` asserts one hard-cap
  procedure per `(a,ρ,B,δ)`, fixed before the law, that meets the rate for every
  law in the power-margin class `PowerMargin ν α a`.

The ranges `0 < a ≤ 1/2`, `0 < ρ ≤ 1/4`, `B > 0` and `0 < δ ≤ 1/4` are the
note's standing hypotheses (gaps in `(0,1/2]`). The proofs are in the other
modules of this directory: `Lower.lean` and `Upper.lean`, assembled in `Full.lean`. -/

noncomputable section
open MeasureTheory
namespace ThresholdHC.ConfidenceTransferSteps
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

/-- Note (17): `r^exp(B,δ) ≥ Ψ(√(ℓ/B))/8192` for every gap law. -/
def PsiConfidenceNullStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B δ : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < δ → δ ≤ 1/4 →
      ENNReal.ofReal (1/8192) * rarePsi μ ρ (ThresholdHC.Confidence.confidenceScale B δ) ≤
        ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ

/-- The remark after note (22): one hard-cap family, fixed before the law, for the
whole power-margin class. -/
def AboveTwoConfidenceFamilyStatement : Prop :=
  ∀ α : ℝ, 2 < α → ∃ C : ℝ, 0 < C ∧
    ∀ a ρ B δ : ℝ, 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < δ → δ ≤ 1/4 →
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      ThresholdHC.HardBudget.PathwiseCap A ⌊B⌋₊ ∧
      ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerMargin ν α a →
        RareBudget ν A ρ B ∧ ∀ q : SignLaw, RarePrior ν ρ q →
          ThresholdHC.Confidence.failureProbability ν A q
            (C * min ρ (Real.sqrt (ρ * Real.log (1/δ)) / (a * Real.sqrt B))) ≤ ENNReal.ofReal δ

/-- Note (22), under both budget conventions; lower constant universal, upper
constant per `α`. -/
def AboveTwoConfidenceStatement : Prop :=
  ∀ α : ℝ, 2 < α → ∃ C : ℝ, 0 < C ∧
    ∀ a ρ B δ : ℝ, 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < δ → δ ≤ 1/4 →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], ExactPowerLaw μ α a →
      let z := min ρ (Real.sqrt (ρ * Real.log (1/δ)) / (a * Real.sqrt B))
      ENNReal.ofReal (z/8192) ≤ ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ ∧
      ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ ≤
        ThresholdHC.ConfidenceProgram.hardConfidenceRadius μ ρ B δ ∧
      ThresholdHC.ConfidenceProgram.hardConfidenceRadius μ ρ B δ ≤ ENNReal.ofReal (C*z)

end ThresholdHC.ConfidenceTransferSteps
