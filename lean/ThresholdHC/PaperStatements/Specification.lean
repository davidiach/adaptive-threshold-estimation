import ThresholdHC.CriticalEntropy.CriticalRareModel
import ThresholdHC.ConfidenceTransfer.CriticalModel
import ThresholdHC.CriticalPsi.Model
import ThresholdHC.RareAboveTwo.Model
import ThresholdHC.UnbiasedConverse.Model
import ThresholdHC.OptimalQuantile.Root
import ThresholdHC.EntropyTailQuantile.Model
import ThresholdHC.SelectionStability.Specification

/-! Target statements for paper claims that had only a paper proof, a
numerical check or an existential constant.

* The critical law `F(d) = (4d)^2` of the critical theorem, with explicit
  constants, the slow divergence remark, and the paper's divergence sequence for
  `Ψ` in the critical theorem's own model.
* The unbiased coefficient `1/16`, attained at every fixed gap by one fresh
  observation, the endpoint case of the nonnegativity proposition, and the
  constant `1/2` for a known point mass.
* The second moment of the observable 713 construction.
* The lower end `1.462554551279` of the paper's decimal bracket for the sharp
  quantile factor, and the selection-stability corollary with the factors
  `20/31` and `1/c_vec`.

The proofs are in the other modules of this directory. -/
noncomputable section
namespace ThresholdHC.PaperStatements
open MeasureTheory ProbabilityTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
open ThresholdHC.UnbiasedConverse
open scoped ENNReal

/-- The critical density `32d` on `(0,1/4]` is the exact power law `F(d) = (4d)^2`. -/
def CriticalPowerLawStatement : Prop :=
  ExactPowerLaw ThresholdHC.ConfidenceTransfer.criticalPositiveLaw 2 (1/4)

/-- The critical theorem's minimax risk is the rare-event minimax risk of that law. -/
def CriticalModelStatement : Prop :=
  ∀ ρ B : ℝ, ThresholdHC.CriticalEntropy.criticalMinimaxRisk ρ B =
    rareMinimaxRisk ThresholdHC.ConfidenceTransfer.criticalPositiveLaw ρ B

/-- The critical theorem with explicit constants on both sides. -/
def CriticalExplicitStatement : Prop :=
  ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    let C := Real.sqrt (ρ * ThresholdHC.CriticalEntropy.criticalLogFactor ρ / B)
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 18 * min ρ C) ≤
        ThresholdHC.CriticalEntropy.criticalMinimaxRisk ρ B ∧
      ThresholdHC.CriticalEntropy.criticalMinimaxRisk ρ B ≤ ENNReal.ofReal (1360000 * min ρ C)

/-- The divergence is slow: `√H < 2.54` for `ρ ≥ 10^{-100}`. -/
def SlowDivergenceStatement : Prop :=
  ∀ ρ : ℝ, (10 : ℝ)⁻¹ ^ 100 ≤ ρ → ρ ≤ 1/4 →
    Real.sqrt (1 + Real.log (1 + Real.log (1/ρ))) < 127/50

/-- The paper's sequence `ρ_n = exp(-exp n)`, `B_n = ρ_n^{-2}` in the critical
theorem's model: the ratio of the minimax risk to `Ψ` is at least a universal
multiple of `√(1 + log(1 + log(1/ρ_n)))`, which is at least `√(1+n)`. -/
def CriticalPsiSequenceStatement : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    let ρ := Real.exp (-Real.exp n)
    let B := 1 / ρ ^ 2
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 18 / 16 * Real.sqrt (1 + Real.log (1 + Real.log (1/ρ))) *
        ThresholdHC.CriticalPsi.criticalPsi ρ (1 / Real.sqrt B)) ≤
      ThresholdHC.CriticalEntropy.criticalMinimaxRisk ρ B ∧
    Real.sqrt (1 + n) ≤ Real.sqrt (1 + Real.log (1 + Real.log (1/ρ)))

/-- (eq:fixed-gap-sharp) At a fixed gap `d`, one fresh observation gives an
unbiased estimator with unit work whose largest variance is `1/(16 d^2)`. -/
def OneFlipStatement : Prop :=
  ∀ d : Gap, ∃ A : AdaptiveEstimator Unit,
    UniformlyUnbiased (Measure.dirac d) A ∧
    UniformVarianceBound (Measure.dirac d) A (1 / (16 * (d : ℝ)^2)) ∧
    UniformBudget (Measure.dirac d) A 1 ∧
    (⨆ q : SignLaw, evariance (populationOutput A) (experimentLaw (Measure.dirac d) A q)) =
      ENNReal.ofReal (1 / (16 * (d : ℝ)^2))

/-- The smallest product of a uniform variance bound and a uniform expected-work
bound over unbiased estimators at the gap law `μ`. -/
def unbiasedVarianceWork (μ : Measure Gap) [IsProbabilityMeasure μ] : ℝ≥0∞ :=
  sInf {t | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R) (V W : ℝ),
    0 ≤ V ∧ 0 ≤ W ∧ UniformlyUnbiased μ A ∧ UniformVarianceBound μ A V ∧
    UniformBudget μ A W ∧ t = ENNReal.ofReal (V * W)}

/-- Equality in the unbiased converse at every fixed gap: `inf VW = I_μ^2/16`. -/
def FixedGapEqualityStatement : Prop :=
  ∀ d : Gap, unbiasedVarianceWork (Measure.dirac d) =
    ENNReal.ofReal ((∫ x : Gap, (x : ℝ)⁻¹ ∂Measure.dirac d)^2 / 16)

/-- `1/16` cannot be increased in a bound valid for every gap law. -/
def UnbiasedSharpStatement : Prop :=
  ∀ c : ℝ,
    (∀ (μ : Measure Gap) [IsProbabilityMeasure μ], Integrable (fun d : Gap => (d : ℝ)⁻¹) μ →
      ENNReal.ofReal (c * (∫ d : Gap, (d : ℝ)⁻¹ ∂μ)^2) ≤ unbiasedVarianceWork μ) ↔
    c ≤ 1/16

/-- Proposition prop:bounded, second sentence: at the gap `1/2`, one observation
is an unbiased `[0,1]`-valued estimator with unit work. -/
def HalfGapUnbiasedStatement : Prop :=
  ∃ A : AdaptiveEstimator Unit,
    (∀ z, 0 ≤ populationOutput A z ∧ populationOutput A z ≤ 1) ∧
    UniformlyUnbiased (Measure.dirac (⟨1/2, by norm_num⟩ : Gap)) A ∧
    UniformBudget (Measure.dirac (⟨1/2, by norm_num⟩ : Gap)) A 1

/-- With the law known, a point mass has minimax RMS risk at most half its modulus. -/
def PointMassUpperStatement : Prop :=
  ∀ (g : Gap) (B : ℝ), 1 ≤ B →
    minimaxRisk (Measure.dirac g) B ≤
      ENNReal.ofReal (modulus (Measure.dirac g) (1 / Real.sqrt B) / 2)

/-- Theorem 2.2's moment sentence for the observable 713 construction:
`sup_q E Y^2 ≤ 23 I_μ` and `sup_q E T ≤ 31 I_μ`, for one unbiased algorithm. -/
def SecondMomentStatement : Prop :=
  ∃ A : AdaptiveEstimator ℕ,
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      Integrable (fun d : Gap => (d : ℝ)⁻¹) μ →
      UniformlyUnbiased μ A ∧
      (∀ q : SignLaw, (∫⁻ z, ENNReal.ofReal ((populationOutput A z)^2) ∂experimentLaw μ A q) ≤
        ENNReal.ofReal (23 * ∫ d : Gap, (d : ℝ)⁻¹ ∂μ)) ∧
      UniformBudget μ A (31 * ∫ d : Gap, (d : ℝ)⁻¹ ∂μ)

/-- The sharp finite-vector quantile factor exceeds `1.462554551279`. -/
def RootLowerStatement : Prop :=
  (1462554551279/1000000000000 : ℝ) < ThresholdHC.OptimalQuantile.scalarRoot

/-- Some finitely supported law has `Q > 1.462554551279 K`. -/
def FiniteRatioStatement : Prop :=
  ∃ (μ : Measure Gap) (_ : IsProbabilityMeasure μ), μ.support.Finite ∧
    ∃ ρ B : ℝ, 0 < ρ ∧ ρ ≤ 1/4 ∧ 0 < B ∧
      ENNReal.ofReal (1462554551279/1000000000000) * ThresholdHC.EntropyTail.selection μ ρ B <
        ThresholdHC.EntropyTailQuantile.closedQuantileValue μ ρ B

/-- The selection-stability corollary with the quantile choice `L = 20Q/31`, `U = Q`. -/
def StabilityQuantileStatement : Prop :=
  ∀ (μ μ₀ : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ₀]
    (T : Gap → Gap), Measurable T → ∀ {r η ρ B : ℝ}, 1 ≤ r → 0 < ρ → ρ ≤ 1/4 → 0 < B →
    tvDist μ μ₀ / 2 ≤ η →
    (∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ)) →
    (∀ j, T ⁻¹' ThresholdHC.EntropyTail.band j = ThresholdHC.EntropyTail.band j) →
    let Q := (ThresholdHC.EntropyTailQuantile.closedQuantileValue (μ₀.map T) ρ B).toReal
    max 0 (20/31*Q - η) ≤ (ThresholdHC.EntropyTail.selection μ ρ B).toReal ∧
      (ThresholdHC.EntropyTail.selection μ ρ B).toReal ≤ min ρ (r*Q + η)

/-- The same corollary with the sharp lower endpoint `Q/c_vec`. -/
def StabilitySharpStatement : Prop :=
  ∀ (μ μ₀ : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ₀]
    (T : Gap → Gap), Measurable T → ∀ {r η ρ B : ℝ}, 1 ≤ r → 0 < ρ → ρ ≤ 1/4 → 0 < B →
    tvDist μ μ₀ / 2 ≤ η →
    (∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ)) →
    (∀ j, T ⁻¹' ThresholdHC.EntropyTail.band j = ThresholdHC.EntropyTail.band j) →
    let Q := (ThresholdHC.EntropyTailQuantile.closedQuantileValue (μ₀.map T) ρ B).toReal
    max 0 (Q / ThresholdHC.OptimalQuantile.scalarRoot - η) ≤
        (ThresholdHC.EntropyTail.selection μ ρ B).toReal ∧
      (ThresholdHC.EntropyTail.selection μ ρ B).toReal ≤ min ρ (r*Q + η)

end ThresholdHC.PaperStatements
