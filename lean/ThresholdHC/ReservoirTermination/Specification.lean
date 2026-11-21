import ThresholdHC.Tier5.Model
import ThresholdHC.Tier6.AlgorithmModel

/-!
# Countable-reservoir termination counterexample: target statements

Source: the research note `research/2026-10-27-minimax-audit/formal/stopping_bridge.tex`,
Proposition (One-law finite work does not transfer termination), lines 9-18, and the
interior-gap remark after its proof (lines 48-53); summarized in
`research/2026-10-27-minimax-audit/FINAL_REPORT.md` (lines 21-27) and
`research/2026-10-27-minimax-audit/formal/MODEL_EXTENSION_SPEC.md` (lines 7-15, Target N).

Fresh iid coins with deterministic gap `D`, sign prior `1/2 + eta` under `P` and
`1/2 - eta` under `Q`. Each coin is queried once and the experiment stops the first time
the plus-minus-one walk of the observed bits `sum (2 X_i - 1)` reaches `+1`. The paper's numbers are
`E_P T = 4` and `Q(T = infinity) = 2/5` at `D = 1/2`, `eta = 1/8`, and `E_P T = 8`,
`Q(T = infinity) = 2/9` at `D = 1/4`.

Formal reading. The experiment is the Tier 5 unrestricted creation model: the policy
`walkPolicy` queries the never-used label equal to the number of observations so far and
stops once the walk equals one. Every realization of its finite-prefix laws
(`RealizesCreationPrefixes`, constant environment) is covered; the iid structure of the
observed bits is derived, not assumed. `T = infinity` is `RunsForever`, and `E T` is the
lower integral of `totalProcessWork`. The general symmetric law gives work
`1/(4 d eta)` and nontermination probability `8 d eta / (1 + 4 d eta)`. It assumes
`eta < 1/2` only so that both observed-bit parameters are strictly inside `(0,1)`, which
the likelihood-ratio tilt of the proof uses. The same formulas hold at `eta = 1/2`
by a direct calculation; that case is not Lean-checked.

`CreationTwoLawStoppingStatement` is the Tier 3 two-law stopping transfer
(`Tier3.UnboundedStoppingStatement`) with the finite family `Fin m` replaced by created
natural-number labels and seed-independent `d eta : ℕ → ℝ`; its negation is the refuted
naive bridge. `ReservoirCounterexampleStatement` states the paper's proposition as an
explicit existence claim in the bare creation model, and `OriginalExperimentStatement`
restates it in the Tier 6 experiment.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ReservoirTermination
open ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6

/-- Successes minus failures of an observed history. -/
def walkValue (xs : List Bool) : ℤ := (xs.count true : ℤ) - (xs.count false : ℤ)

/-- Query a never-used coin (label = observations so far); stop the first time
the plus-minus-one walk of observed bits equals one. -/
def walkPolicy (xs : List Bool) : Option ℕ :=
  if walkValue xs = 1 then none else some xs.length

/-- Realized paths on which the walk policy never stops (`T = infinity`). -/
def RunsForever {Ω : Type} (tape : Ω → ProcessTape) : Set Ω :=
  {ω | ∀ n, walkPolicy (processHistory (tape ω) n) ≠ none}

/-- Every realization, fresh coins of magnitude `d`, sign prior `1/2 + eta` or
`1/2 - eta`. The restriction `eta < 1/2` is used only by the proof's likelihood-ratio
tilt; the case `eta = 1/2` is not stated. -/
def WalkFirstPassageStatement : Prop :=
  ∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (seed : Ω → Seed) (tape : Ω → ProcessTape) (d η : ℝ),
    (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    0 < d → d ≤ 1/2 → 0 < η → η < 1/2 →
    (RealizesCreationPrefixes μ ν seed tape (fun _ => walkPolicy)
        (fun _ _ => d) (fun _ _ => 1/2 + η) →
      ν (RunsForever tape) = 0 ∧
      (∫⁻ ω, totalProcessWork (tape ω) ∂ν) = ENNReal.ofReal (1 / (4 * d * η))) ∧
    (RealizesCreationPrefixes μ ν seed tape (fun _ => walkPolicy)
        (fun _ _ => d) (fun _ _ => 1/2 - η) →
      ν (RunsForever tape) = ENNReal.ofReal (8 * d * η / (1 + 4 * d * η)) ∧
      (∫⁻ ω, totalProcessWork (tape ω) ∂ν) = ∞)

/-- The paper's proposition: `D = 1/2`, priors `5/8` against `3/8`. -/
def HalfGapExampleStatement : Prop :=
  (∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (seed : Ω → Seed) (tape : Ω → ProcessTape),
    (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    RealizesCreationPrefixes μ P seed tape (fun _ => walkPolicy)
      (fun _ _ => 1/2) (fun _ _ => 5/8) →
    P (RunsForever tape) = 0 ∧ (∫⁻ ω, totalProcessWork (tape ω) ∂P) = 4) ∧
  (∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (Q : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
    (seed : Ω → Seed) (tape : Ω → ProcessTape),
    (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    RealizesCreationPrefixes μ Q seed tape (fun _ => walkPolicy)
      (fun _ _ => 1/2) (fun _ _ => 3/8) →
    Q (RunsForever tape) = 2/5)

/-- Interior-gap variant: `D = 1/4`, same priors; work `8`, nontermination `2/9`. -/
def QuarterGapExampleStatement : Prop :=
  (∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (seed : Ω → Seed) (tape : Ω → ProcessTape),
    (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    RealizesCreationPrefixes μ P seed tape (fun _ => walkPolicy)
      (fun _ _ => 1/4) (fun _ _ => 5/8) →
    P (RunsForever tape) = 0 ∧ (∫⁻ ω, totalProcessWork (tape ω) ∂P) = 8) ∧
  (∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (Q : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
    (seed : Ω → Seed) (tape : Ω → ProcessTape),
    (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    RealizesCreationPrefixes μ Q seed tape (fun _ => walkPolicy)
      (fun _ _ => 1/4) (fun _ _ => 3/8) →
    Q (RunsForever tape) = 2/9)

/-- `Tier3.UnboundedStoppingStatement` with `Fin m` replaced by created natural-number
labels: seed-independent magnitudes and prior offsets, and every Tier 5 regularity
hypothesis. -/
def CreationTwoLawStoppingStatement : Prop :=
  ∀ (Seed Ω : Type) [MeasurableSpace Seed] [MeasurableSpace Ω]
    (μ : Measure Seed) (P Q : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (seed : Ω → Seed) (tape : Ω → ProcessTape)
    (pol : Seed → List Bool → Option ℕ) (d η : ℕ → ℝ),
    Measurable seed → (∀ n b, MeasurableSet {ω | tape ω n = b}) →
    MeasurableCreationPolicy pol →
    RealizesCreationPrefixes μ P seed tape pol (fun _ => d) (fun _ i => 1/2 + η i) →
    RealizesCreationPrefixes μ Q seed tape pol (fun _ => d) (fun _ i => 1/2 - η i) →
    (∀ i, 0 < d i ∧ d i ≤ 1/2) → (∀ i, 0 ≤ η i ∧ η i ≤ 1/8) →
    (∫⁻ ω, totalProcessWork (tape ω) ∂P) < ∞ →
    (∀ᵐ ω ∂P, ∃ n, pol (seed ω) (processHistory (tape ω) n) = none) ∧
    (∀ᵐ ω ∂Q, ∃ n, pol (seed ω) (processHistory (tape ω) n) = none)

/-- The naive countable-reservoir bridge is false. -/
def NaiveBridgeFailsStatement : Prop := ¬ CreationTwoLawStoppingStatement

/-- The paper's proposition as an explicit existence statement in the bare creation
model, with a trivial seed. -/
def ReservoirCounterexampleStatement : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P Q : Measure Ω) (tape : Ω → ProcessTape),
    IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
    (∀ n b, MeasurableSet {ω | tape ω n = b}) ∧
    RealizesCreationPrefixes (Measure.dirac ()) P (fun _ => ()) tape (fun _ => walkPolicy)
      (fun _ _ => 1/2) (fun _ _ => 5/8) ∧
    RealizesCreationPrefixes (Measure.dirac ()) Q (fun _ => ()) tape (fun _ => walkPolicy)
      (fun _ _ => 1/2) (fun _ _ => 3/8) ∧
    P (RunsForever tape) = 0 ∧ (∫⁻ ω, totalProcessWork (tape ω) ∂P) = 4 ∧
    Q (RunsForever tape)ᶜ = 3/5 ∧ Q (RunsForever tape) = 2/5 ∧
    (∫⁻ ω, totalProcessWork (tape ω) ∂Q) = ∞

/-- The walk policy as a Tier 6 adaptive estimator with a trivial seed. -/
def walkEstimator : AdaptiveEstimator Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  policy := fun _ => walkPolicy
  policy_measurable := fun _ _ => measurableSet_eq_fun measurable_const measurable_const
  output := fun _ => 0
  output_measurable := measurable_const

/-- The constant sign law. -/
def constantSignLaw (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : SignLaw :=
  ⟨fun _ => p, measurable_const, fun _ => hp⟩

/-- The gap one half. -/
def halfGap : Gap := ⟨1/2, by norm_num⟩

/-- The gap one quarter. -/
def quarterGap : Gap := ⟨1/4, by norm_num⟩

/-- The same counterexample in the original Tier 6 experiment, with the point-mass gap
laws at one half and one quarter. -/
def OriginalExperimentStatement : Prop :=
  expectedWork (Measure.dirac halfGap) walkEstimator (constantSignLaw (5/8) (by norm_num)) = 4 ∧
  experimentLaw (Measure.dirac halfGap) walkEstimator (constantSignLaw (3/8) (by norm_num))
    (RunsForever (Ω := PopulationSeed Unit × ProcessTape) Prod.snd) = 2/5 ∧
  expectedWork (Measure.dirac halfGap) walkEstimator (constantSignLaw (3/8) (by norm_num)) = ∞ ∧
  expectedWork (Measure.dirac quarterGap) walkEstimator (constantSignLaw (5/8) (by norm_num)) = 8 ∧
  experimentLaw (Measure.dirac quarterGap) walkEstimator (constantSignLaw (3/8) (by norm_num))
    (RunsForever (Ω := PopulationSeed Unit × ProcessTape) Prod.snd) = 2/9 ∧
  ∀ B : ℝ, ¬ UniformBudget (Measure.dirac halfGap) walkEstimator B

end ThresholdHC.ReservoirTermination
