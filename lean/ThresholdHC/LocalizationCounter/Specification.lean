import ThresholdHC.RareAboveTwo.Model
import ThresholdHC.Observable713.Controller
import ThresholdHC.Proofs.Tier2.ClassifierModel
import ThresholdHC.Proofs.Tier2.ClassifierProbability
import ThresholdHC.Uniform713.Estimator

/-! Target statements for two auxiliary results of the v6 appendix on localized
rare-event scales, `paper/v6/appendix-localization.tex`.

* Theorem `loc:thm:counter` (a counterexample to the proposed rescaling). With
  `0 < ρ ≤ 1/4`, `a = 1/4`, `d = ρ²`, `μ_ρ = ρ δ_d + (1-ρ) δ_a` and `B = ρ^{-4}`,
  the rare minimax RMS risk is at least `ρ/100`, while the heuristic
  `H_{μ,ρ}(h) = ρ ω_μ(h/√ρ)` of eq. `loc:eq:heuristic` equals
  `ρ² + 4(1-ρ)ρ^{5/2} = O(ρ²)` at `h = B^{-1/2}`. The minimax risk
  `rareMinimaxRisk` is the one of the unchanged observable rare-event experiment
  (`RareAboveTwo.Model`): magnitudes and signs are hidden, rarity is a bound on
  the integral of the sign law and the budget bounds the expected number of
  actual flips under every rare prior. `ω_μ` is `Tier6.modulus`.
* Proposition `loc:prop:noise` (why the original unmodified variance is not
  rarity-scaled): at one fixed negative coin of magnitude `d < 1/2`, the level-0
  term of the geometric single-term estimator alone forces the second moment
  `E Y² ≥ (1/2-d)/(1-2^{-1/2})`. Here `2^{-1/2}` is `rLevel`.

Three forms of the noise floor are stated. `Observable713NoiseFloorStatement` is
the variance form in the unchanged observable experiment, for the 713-threshold
estimator `Observable713.observableEstimator`, the untruncated single-term
estimator whose unbiasedness is proved for every gap law with integrable `1/d`
(in particular at the Dirac law used here). Its thresholds are
`√((1/4+log(N/n))/n)`, not the paper's original `√([1+log(n/k)]/k)`.
`OriginalSecondMomentFloorStatement` is the second-moment floor for the paper's
original (`k₁ = k₂ = 1`) untruncated estimator in the single-coin sampling model;
neither its unbiasedness nor its square integrability is claimed, so the floor is
a lower bound on a possibly infinite extended second moment. `TruncatedNoiseFloorStatement` is the truncated
form in the frozen finite model of `Statements2` with the original thresholds.

The claims of the same appendix that are not formalized here are the fixed
uniform-law failure after Theorem `loc:thm:power`, Proposition `loc:prop:Gamma`
and Proposition `loc:prop:generalupper`. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.LocalizationCounter
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

/-- The fixed magnitude `a = 1/4` of Theorem `loc:thm:counter`. -/
def quarterGap : Gap := ⟨1/4, by norm_num, by norm_num⟩

/-- The law `μ_ρ = ρ δ_d + (1-ρ) δ_{1/4}`; the theorem takes `d = ρ²`. -/
def counterLaw (ρ : ℝ) (d : Gap) : Measure Gap :=
  ENNReal.ofReal ρ • Measure.dirac d + ENNReal.ofReal (1 - ρ) • Measure.dirac quarterGap

/-- The proposed heuristic `H_{μ,ρ}(h) = ρ ω_μ(h/√ρ)` of eq. `loc:eq:heuristic`. -/
def heuristic (μ : Measure Gap) (ρ h : ℝ) : ℝ := ρ * modulus μ (h / Real.sqrt ρ)

/-- The law of Theorem `loc:thm:counter` is a probability law, so the equation
hypothesis on `μ` in the two counterexample targets can be met. -/
def CounterLawProbabilityStatement : Prop :=
  ∀ (ρ : ℝ) (d : Gap), 0 ≤ ρ → ρ ≤ 1 → IsProbabilityMeasure (counterLaw ρ d)

/-- Theorem `loc:thm:counter` with `B = ρ^{-4}`, written `1/ρ^4`, and
`ρ^{5/2}` written `ρ²√ρ`. The bound `R ≤ ρ/2` (the constant estimator `ρ/2`)
together with `ρ/100 ≤ R` records that the minimax error is of order `ρ`, and
`H ≤ 3ρ²` records `H = O(ρ²)`. -/
def CounterexampleStatement : Prop :=
  ∀ (ρ : ℝ) (d : Gap), 0 < ρ → ρ ≤ 1/4 → (d : ℝ) = ρ^2 →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], μ = counterLaw ρ d →
      ENNReal.ofReal (ρ/100) ≤ rareMinimaxRisk μ ρ (1/ρ^4) ∧
      rareMinimaxRisk μ ρ (1/ρ^4) ≤ ENNReal.ofReal (ρ/2) ∧
      heuristic μ ρ (1 / Real.sqrt (1/ρ^4)) = ρ^2 + 4*(1-ρ)*ρ^2*Real.sqrt ρ ∧
      heuristic μ ρ (1 / Real.sqrt (1/ρ^4)) ≤ 3*ρ^2

/-- The last sentence of Theorem `loc:thm:counter`: the heuristic can
underestimate the minimax error by an unbounded factor. For every factor `K`,
small enough `ρ` make the risk exceed `K` times the heuristic. -/
def CounterUnboundedStatement : Prop :=
  ∀ K : ℝ, 0 < K → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ (ρ : ℝ) (d : Gap), 0 < ρ → ρ ≤ ρ₀ → ρ ≤ 1/4 → (d : ℝ) = ρ^2 →
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], μ = counterLaw ρ d →
        ENNReal.ofReal (K * heuristic μ ρ (1 / Real.sqrt (1/ρ^4))) <
          rareMinimaxRisk μ ρ (1/ρ^4)

/-- Every coin negative: the sign law identically zero. -/
def negativeSign : SignLaw := ⟨fun _ => 0, measurable_const, fun _ => ⟨le_rfl, zero_le_one⟩⟩

/-- Proposition `loc:prop:noise`, untruncated variance form, for the 713-threshold
variant of the single-term estimator, `Observable713.observableEstimator`, whose
classifier thresholds are `√((1/4+log(N/n))/n)` rather than the paper's original
`√([1+log(n/k)]/k)`. The experiment is the unchanged observable experiment with
the Dirac magnitude law at `d` and every coin negative. The conjuncts are square
integrability, unbiasedness (`E Y = θ = 0`), the variance floor (Mathlib's
`evariance`) and its positivity. -/
def Observable713NoiseFloorStatement : Prop :=
  ∀ d : Gap, (d : ℝ) < 1/2 →
    MemLp (populationOutput Observable713.observableEstimator) 2
        (experimentLaw (Measure.dirac d) Observable713.observableEstimator negativeSign) ∧
    (∫ z, populationOutput Observable713.observableEstimator z
        ∂experimentLaw (Measure.dirac d) Observable713.observableEstimator negativeSign) = 0 ∧
    ENNReal.ofReal ((1/2 - (d : ℝ)) / (1 - rLevel)) ≤
      evariance (populationOutput Observable713.observableEstimator)
        (experimentLaw (Measure.dirac d) Observable713.observableEstimator negativeSign) ∧
    0 < (1/2 - (d : ℝ)) / (1 - rLevel)

/-- Proposition `loc:prop:noise`, second-moment floor for the original
(`k₁ = k₂ = 1`) untruncated geometric single-term estimator at one fixed negative
coin, in the single-coin sampling model: an independent geometric level and one
iid Bernoulli tape with success probability `1/2-d`. Neither unbiasedness nor
square integrability (finiteness of this second moment) of this estimator is
claimed here; the floor is a lower bound on a possibly infinite extended second
moment. `E Y = 0` and the variance form are in the 713 variant
`Observable713NoiseFloorStatement`. -/
def OriginalSecondMomentFloorStatement : Prop :=
  ∀ d : Gap, (d : ℝ) < 1/2 →
    ENNReal.ofReal ((1/2 - (d : ℝ)) / (1 - rLevel)) ≤
      ∫⁻ x, ENNReal.ofReal ((Uniform713.estimator
          (fun j ω => Tier2.Model.decision
            (fun k => Uniform713.dyadicMean Tier2.observations k ω) j) x) ^ 2)
        ∂Uniform713.samplingMeasure
          (Tier2.tapeMeasure (ObservableSimulation.gapParameter false d))

/-- Proposition `loc:prop:noise`, truncation at level `L`, original thresholds
`k₁ = k₂ = 1`, in the frozen finite model of `Statements2`. There
`E Y_L² = secondMomentK 1 1 L d false`, `E Y_L = Σ_{l ≤ L} E Δ_l` and
`E Z_{2^L}` is the `zK` sum. The first conjunct is the second-moment floor. The
second conjunct encodes `Var Y_L` as `secondMomentK - (Σ_l E Δ_l)²`; it is the
telescoped restatement of the first conjunct (subtract the square of
`E Y_L = E Z_{2^L}`, Lemma 7 telescoping), not new content. -/
def TruncatedNoiseFloorStatement : Prop :=
  ∀ (L : ℕ) (d : ℝ), 0 < d → d < 1/2 →
    (1/2 - d) / (1 - rLevel) ≤ secondMomentK 1 1 L d false ∧
    (1/2 - d) / (1 - rLevel) -
        (∑ x : Fin (2^L) → Bool, streamProb (coinP d false) x * zK 1 1 L x)^2 ≤
      secondMomentK 1 1 L d false -
        (∑ l ∈ Finset.range (L+1), ∑ x : Fin (2^L) → Bool,
          streamProb (coinP d false) x * deltaK 1 1 l x)^2

end ThresholdHC.LocalizationCounter
