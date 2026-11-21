import ThresholdHC.ContinuousObserved.StateParameter
import ThresholdHC.ContinuousObserved.LowerReduction
import ThresholdHC.ContinuousObserved.UniformGaps

/-!
# Specification: the nested-simulation class satisfies the Giles--Haji-Ali assumptions

Source: `paper/v6/core.tex`, Corollary `cor:nested` (Critical nested-simulation
obstruction), final sentence: every measurable conditional model with
`U ~ Unif[0,1]`, `X ∈ {-1,1}`, `D(U) = |E[X | U]| / 2 ~ Unif(0,1/4]` and no
cross-state regularity satisfies Assumptions 2.1 and 2.4 of Giles--Haji-Ali
(`\cite{gileshajiali}`, arXiv:1802.05016v2), with uniform constants.
The same claim appears in `paper/v6/core.tex`, Proposition `prop:continuous`
(bounded-density and normalized conditional-moment assumptions 2.1 and 2.4,
with constants independent of the error scale). The calculation closes the
proof of `prop:continuous` in `core.tex` and is repeated in
`paper/v6/appendix-continuous-observed.tex`, in the regularity paragraph after
the proof of `thm:continuous-observed-verified`, which verifies the assumptions
stated in `prop:continuous`: `|m| = 2D`, `Var(X | U) = 1 - 4D^2 ≥ 3/4`,
`|X - m| ≤ 3/2`, and the density `f_Z ≤ 2`.

The two predicates `GHABoundedDensity` and `GHAStandardizedMoment` transcribe
the in-repository paraphrases of the Giles--Haji-Ali assumptions
(`inputs/next-phase/baseline/Adaptive_Threshold_v4/review/SOURCE_AUDIT.md`,
Assumptions 2.1 and 2.4; `research/2026-10-27-minimax-audit/LITERATURE_AUDIT.md`;
`research/2026-10-27-route-a/sources.md`). They have not been checked here
against the verbatim text of arXiv:1802.05016v2 (pp. 5-6).

Conditional laws are represented by a state-indexed kernel `K : Ω → Measure ℝ`
(the law of the real observation `X` given the outer state), not by a
conditional expectation on a joint law. The guards in the predicates
(a.e.-measurability, probability kernel, positive conditional standard
deviation, integrability) exclude conventions for undefined values: for a
non-a.e.-measurable map from a nonzero measure, `Measure.map` returns a Dirac
measure; an undefined Bochner integral is `0`; and `x / 0 = 0`.
-/

noncomputable section
namespace ThresholdHC.NestedAssumptions
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.ObservedState ThresholdHC.ObservableSimulation
  ThresholdHC.ContinuousObserved

/-- `E[X | Y = ω]`, where `K ω` is the conditional law of the real observation `X`. -/
def condMean {Ω : Type*} (K : Ω → Measure ℝ) (ω : Ω) : ℝ := ∫ x, x ∂K ω

/-- `σ(ω) = √Var[X | Y = ω]`. -/
def condSD {Ω : Type*} (K : Ω → Measure ℝ) (ω : Ω) : ℝ := Real.sqrt (variance id (K ω))

/-- `|E[X | Y = ω]| / σ(ω)`, the normalized absolute conditional mean. -/
def normalizedMean {Ω : Type*} (K : Ω → Measure ℝ) (ω : Ω) : ℝ :=
  |condMean K ω| / condSD K ω

/-- Transcription of the in-repository paraphrase of Giles--Haji-Ali Assumption 2.1
(`SOURCE_AUDIT.md`, `LITERATURE_AUDIT.md`): the normalized absolute conditional mean
`|E[X | Y]| / σ(Y)` has a density, and some version of it is at most `ρ₀` on `[0, δ₀]`.
Not yet checked against the verbatim text of arXiv:1802.05016v2. -/
def GHABoundedDensity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (K : Ω → Measure ℝ)
    (ρ₀ δ₀ : ℝ) : Prop :=
  0 < δ₀ ∧ AEMeasurable (normalizedMean K) P ∧
    ∃ f : ℝ → ℝ≥0∞, Measurable f ∧ P.map (normalizedMean K) = volume.withDensity f ∧
      ∀ z ∈ Icc (0 : ℝ) δ₀, f z ≤ ENNReal.ofReal ρ₀

/-- Transcription of the in-repository paraphrase of Giles--Haji-Ali Assumption 2.4
(`SOURCE_AUDIT.md`, `LITERATURE_AUDIT.md`), read `P`-almost everywhere: at order `q > 2`
the conditional standardized `q`-th central absolute moment is at most `C`.
Not yet checked against the verbatim text of arXiv:1802.05016v2. -/
def GHAStandardizedMoment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Ω → Measure ℝ) (q C : ℝ) : Prop :=
  2 < q ∧ ∀ᵐ ω ∂P, IsProbabilityMeasure (K ω) ∧ 0 < condSD K ω ∧
    Integrable (fun x => (|x - condMean K ω| / condSD K ω) ^ q) (K ω) ∧
    ∫ x, (|x - condMean K ω| / condSD K ω) ^ q ∂K ω ≤ C

/-- The conditional law of `X ∈ {-1,1}` at state `u` when `P(X = 1 | U = u) = p u`. -/
def binaryLaw (p : unitInterval → unitInterval) (u : unitInterval) : Measure ℝ :=
  (bernoulliMeasure true false (p u)).map binaryValue

/-- The class of `cor:nested`: a measurable conditional model, with `U` uniform on
`[0,1]`, whose half conditional-mean magnitude `D(U) = |E[X | U]| / 2` is uniform on
`(0, 1/4]`. -/
def NestedModel (p : unitInterval → unitInterval) : Prop :=
  Measurable p ∧
    volume.map (fun u => |condMean (binaryLaw p) u| / 2) =
      (4 : ℝ≥0∞) • volume.restrict (Ioc (0 : ℝ) (1 / 4))

/-- The class of `cor:nested` is inhabited, so the class-wide statements are not vacuous. -/
def NestedModelNonemptyStatement : Prop := ∃ p : unitInterval → unitInterval, NestedModel p

/-- `cor:nested`, final sentence: every model of the class satisfies the transcribed
Assumption 2.1 with `ρ₀ = 2` at every `δ₀ > 0`, and the transcribed Assumption 2.4 at
every `q > 2` with `C = 3^(q/2)`. -/
def NestedAssumptionsStatement : Prop :=
  ∀ p : unitInterval → unitInterval, NestedModel p →
    (∀ δ₀ : ℝ, 0 < δ₀ → GHABoundedDensity volume (binaryLaw p) 2 δ₀) ∧
    ∀ q : ℝ, 2 < q → GHAStandardizedMoment volume (binaryLaw p) q ((3 : ℝ) ^ (q / 2))

/-- With uniform constants: the constants are chosen before the model. -/
def UniformConstantsStatement : Prop :=
  ∃ ρ₀ δ₀ q C : ℝ, ∀ p : unitInterval → unitInterval, NestedModel p →
    GHABoundedDensity volume (binaryLaw p) ρ₀ δ₀ ∧ GHAStandardizedMoment volume (binaryLaw p) q C

/-- Every sign-cell design of `uniform_confidence_lower` and `uniform_rms_lower`, with
every sign array, is a model of the class. -/
def HardDesignStatement : Prop :=
  ∀ (h : Gap) (δ : ℝ) (D : CellDesign uniformGaps h δ) (s : Fin D.count → Bool),
    NestedModel (stateParameter (CellDesign.queryDesign uniformGaps h δ D) s)

/-- The class kernel of a hard design is the `binaryValue`-pushforward of the per-query
observation law used by `prefixExpectation` (`ContinuousObserved/PrefixLaw.lean`). -/
def HardDesignLawStatement : Prop :=
  ∀ (h : Gap) (δ : ℝ) (D : CellDesign uniformGaps h δ) (s : Fin D.count → Bool)
    (u : unitInterval),
    binaryLaw (stateParameter (CellDesign.queryDesign uniformGaps h δ D) s) u =
      (bernoulliMeasure true false (gapParameter (s (D.cell u)) (D.gap u))).map binaryValue

end ThresholdHC.NestedAssumptions
