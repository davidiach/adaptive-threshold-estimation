import ThresholdHC.RobustContinuation.Clipping
import ThresholdHC.UnbiasedConverse.Model

/-! Target statements for the clipping-boundary note,
`research/2026-10-27-nonlinear-population/audit/CLIPPING_BOUNDARY.tex`
(section `sec:clipping-boundary`), as summarized in `docs/SECONDARY_CLAIMS.md`.

The note writes `Π_ρ(x) = min{ρ, max{0,x}}` for a known clipping interval and a
true parameter `θ ∈ [0,ρ]`. Here `Π_ρ` is `clipEstimate ρ x = max 0 (min ρ x)`,
which agrees with `Π_ρ` whenever `0 ≤ ρ`, and `0 ≤ ρ` follows from `0 ≤ θ ≤ ρ`.

* Proposition (a bounded-kurtosis transfer): if `F` is unbiased for `θ`, has
  finite variance `σ²` and `E(F-θ)⁴ ≤ Kσ⁴` with `1 ≤ K`, then
  `E(Π_ρ(F)-θ)² ≥ min{σ²,ρ²}/(256K²)`. The finite-variance and fourth-moment
  premises are `MemLp F 4 P` together with a Bochner fourth-moment bound, and
  `σ²` is `ProbabilityTheory.variance F P`; the paper's premise already forces
  a finite fourth moment. `KurtosisTransferStatement` is the squared form and
  `KurtosisRMSStatement` the RMS form `min(ρ,σ)/(16K)` of `SECONDARY_CLAIMS.md`.
* The uniform corollary after the proposition: if the premises hold for every
  `q` with one common `K`, the clipped RMS is at least
  `(16K)⁻¹ min{ρ, √(sup_q Var_q F)}`. Here every `q` is read as every rare sign
  law (`RarePrior μ ρ q`), which is what places the target `signMean μ q.val`
  in `[0,ρ]`; taking `ρ ≥ 1` recovers the whole sign class, since the sign mean
  is at most `1`. The supremum is taken in `ℝ≥0∞` over `evariance`, so an
  infinite supremum gives the floor `ρ/(16K)`. This is
  `UniformClippedFloorStatement`, stated for the clipped estimator of the
  original experiment.
* Proposition (why there is no unrestricted variance transfer): independent
  seed noise `Z`, equal to `0` with probability `1-ε` and to `±M` with
  probability `ε/2` each, leaves `F = F₀ + Z` unbiased and adds `εM²` to its
  variance, and the clipped squared risk of `F` exceeds the raw squared risk
  of `F₀` by at most `ερ²`.
  `NoiseCounterexampleStatement` is the abstract form, with independence given
  by the product law. `NoisyEstimatorStatement` is the same construction in the
  original experiment: the noise is an extra seed coordinate, so the policy and
  the expected work are unchanged. Its last three clauses are the formal
  reading of the note's remark that the noise respects the inherited additive
  class: the uniform unbiasedness, budget and variance-bound properties used
  by `UnbiasedConverse` transfer, and a uniform variance bound `V ≥ 0` becomes
  `V + εM²`. Membership in the structural additive class of the note's
  construction is not formalized. The mean, variance and risk clauses carry only the
  hypotheses each needs.

The proofs are in `Full.lean`. -/
noncomputable section
namespace ThresholdHC.ClippingBoundary
open MeasureTheory
open ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.RareAboveTwo
  ThresholdHC.RobustContinuation

/-- Seed noise: for `0 ≤ ε ≤ 1`, `0` with probability `1-ε` and `±M` with
probability `ε/2` each. -/
def seedNoise (ε M : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - ε) • Measure.dirac (0 : ℝ) + ENNReal.ofReal (ε / 2) • Measure.dirac M +
    ENNReal.ofReal (ε / 2) • Measure.dirac (-M)

/-- Proposition (a bounded-kurtosis transfer), squared form:
`E(Π_ρ(F)-θ)² ≥ min{σ²,ρ²}/(256K²)`. -/
def KurtosisTransferStatement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → ℝ) (θ ρ K : ℝ),
    MemLp F 4 P → (∫ ω, F ω ∂P) = θ → 0 ≤ θ → θ ≤ ρ → 1 ≤ K →
    (∫ ω, (F ω - θ) ^ 4 ∂P) ≤ K * ProbabilityTheory.variance F P ^ 2 →
    ENNReal.ofReal (min (ProbabilityTheory.variance F P) (ρ ^ 2) / (256 * K ^ 2)) ≤
      squaredRisk P (fun ω => clipEstimate ρ (F ω)) θ

/-- The same transfer as `SECONDARY_CLAIMS.md` states it: the clipped RMS is at
least `min(ρ,σ)/(16K)`. -/
def KurtosisRMSStatement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → ℝ) (θ ρ K : ℝ),
    MemLp F 4 P → (∫ ω, F ω ∂P) = θ → 0 ≤ θ → θ ≤ ρ → 1 ≤ K →
    (∫ ω, (F ω - θ) ^ 4 ∂P) ≤ K * ProbabilityTheory.variance F P ^ 2 →
    ENNReal.ofReal (min ρ (Real.sqrt (ProbabilityTheory.variance F P)) / (16 * K)) ≤
      rootMeanRisk P (fun ω => clipEstimate ρ (F ω)) θ

/-- The uniform corollary in the original experiment: if the premises hold for
every rare sign law with one common `K`, the clipped rare RMS is at least
`(16K)⁻¹ min{ρ, √(sup_q Var_q F)}`, with the supremum in `ℝ≥0∞`. -/
def UniformClippedFloorStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (ρ K : ℝ), 1 ≤ K →
    (∀ q : SignLaw, RarePrior μ ρ q →
      MemLp (populationOutput A) 4 (experimentLaw μ A q) ∧
      (∫ z, populationOutput A z ∂experimentLaw μ A q) = signMean μ q.val ∧
      (∫ z, (populationOutput A z - signMean μ q.val) ^ 4 ∂experimentLaw μ A q) ≤
        K * ProbabilityTheory.variance (populationOutput A) (experimentLaw μ A q) ^ 2) →
    ENNReal.ofReal (1 / (16 * K)) * min (ENNReal.ofReal ρ)
      ((⨆ (q : SignLaw) (_ : RarePrior μ ρ q),
        ProbabilityTheory.evariance (populationOutput A) (experimentLaw μ A q)) ^ (1/2 : ℝ)) ≤
      rareRisk μ (clippedEstimator A ρ) ρ

/-- Proposition (why there is no unrestricted variance transfer), abstract form:
the noise `Z` is independent of `F₀` through the product law. -/
def NoiseCounterexampleStatement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F₀ : Ω → ℝ) (θ ρ ε M : ℝ),
    MemLp F₀ 2 P → (∫ ω, F₀ ω ∂P) = θ → 0 ≤ θ → θ ≤ ρ → 0 ≤ ε → ε ≤ 1 →
    IsProbabilityMeasure (seedNoise ε M) ∧
    (∫ z, F₀ z.1 + z.2 ∂P.prod (seedNoise ε M)) = θ ∧
    ProbabilityTheory.variance (fun z : Ω × ℝ => F₀ z.1 + z.2) (P.prod (seedNoise ε M)) =
      ProbabilityTheory.variance F₀ P + ε * M ^ 2 ∧
    squaredRisk (P.prod (seedNoise ε M)) (fun z => clipEstimate ρ (F₀ z.1 + z.2)) θ ≤
      squaredRisk P F₀ θ + ENNReal.ofReal (ε * ρ ^ 2)

/-- The same proposition in the original experiment. The noise is an extra seed
coordinate added to the output, so the policy and the expected work are
unchanged. The last three clauses are the formal reading of the note's remark
on the inherited additive class: uniform unbiasedness, uniform budgets, and a
uniform variance bound `V ≥ 0`, which becomes `V + εM²`, transfer. Membership
in the structural additive class is not formalized. -/
def NoisyEstimatorStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (ε M : ℝ), 0 ≤ ε → ε ≤ 1 →
    ∃ A' : AdaptiveEstimator (R × ℝ),
      A'.randomLaw = A.randomLaw.prod (seedNoise ε M) ∧
      (∀ u, A'.policy u = A.policy u.1) ∧
      (∀ z, A'.output z = A.output (z.1.1, z.2) + z.1.2) ∧
      (∀ q : SignLaw,
        expectedWork μ A' q = expectedWork μ A q ∧
        (Integrable (populationOutput A) (experimentLaw μ A q) →
          Integrable (populationOutput A') (experimentLaw μ A' q) ∧
          (∫ z, populationOutput A' z ∂experimentLaw μ A' q) =
            ∫ z, populationOutput A z ∂experimentLaw μ A q) ∧
        (MemLp (populationOutput A) 2 (experimentLaw μ A q) →
          ProbabilityTheory.variance (populationOutput A') (experimentLaw μ A' q) =
            ProbabilityTheory.variance (populationOutput A) (experimentLaw μ A q) + ε * M ^ 2) ∧
        ∀ θ ρ : ℝ, 0 ≤ θ → θ ≤ ρ →
          squaredRisk (experimentLaw μ A' q) (fun z => clipEstimate ρ (populationOutput A' z)) θ ≤
            squaredRisk (experimentLaw μ A q) (populationOutput A) θ +
              ENNReal.ofReal (ε * ρ ^ 2)) ∧
      (UnbiasedConverse.UniformlyUnbiased μ A → UnbiasedConverse.UniformlyUnbiased μ A') ∧
      (∀ W : ℝ, UniformBudget μ A' W ↔ UniformBudget μ A W) ∧
      (∀ V : ℝ, 0 ≤ V → UnbiasedConverse.UniformVarianceBound μ A V →
        UnbiasedConverse.UniformVarianceBound μ A' (V + ε * M ^ 2))

end ThresholdHC.ClippingBoundary
