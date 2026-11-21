import ThresholdHC.DepthObstruction.Specification
import ThresholdHC.ObservableSimulation.OriginalExperiment

/-! Target statements for part 2 of the bounded-depth obstruction: the
elementary bounded polynomial `lem:poly` (An elementary bounded polynomial,
lines 20-85) and the explicit odd-Legendre hard pair of the theorem `thm:cap`
(Feedback does not repair bounded-depth nonidentifiability, lines 87-151) of
`research/2026-10-27-nonlinear-population/upper/proof-body.tex`, also
summarised in `research/2026-10-27-nonlinear-population/FINAL_REPORT.md`
(lines 15-19) and in the row Bounded-depth obstruction of
`docs/SECONDARY_CLAIMS.md`. Part 1, the general per-coin-cap
transcript identity and floor for any matching pair, is the group
`ThresholdHC.DepthObstruction`, whose definitions are reused here.

* `legendre n`: the degree-`n` Legendre polynomial by Rodrigues' formula
  `P_n = (2^n n!)⁻¹ dⁿ/dxⁿ (x²-1)ⁿ`, as in the source (not Mathlib's
  shifted Legendre polynomial).
* `depthSlope K`: `c = P_n'(0)` for `n = 2K+1`.
* `depthPolynomial K`: `u_K = c⁻¹ · divX P_n`, the polynomial with
  `u_K(x) = P_n(x)/(c x)` for `x ≠ 0` and `u_K(0) = 1`; the statement records
  both facts and `c ≠ 0`, so it agrees with the source's definition.
* `depthMoment K`: `m_K = 1/((K+1)(2K+1))`.
* `depthSign K a ρ plus`: the allocations `q_±(d) = (1 ± u_K(d/h))/2 · 1{d ≤ h}`
  with `h = a √ρ`.
* `DepthPolynomialStatement`: `lem:poly`. For `K ≥ 1`, `u_K` is an even
  polynomial of degree `2K` with `|u_K| ≤ 1` on `[0,1]`,
  `∫₀¹ x^(2j+2) u_K = 0` for `j < K` and `∫₀¹ 2x u_K = m_K`. Evenness is stated
  as `u_K(-x) = u_K(x)`.
* `DepthPairStatement`: the pair of `thm:cap` for the exact quadratic law
  (`ExactPowerLaw μ 2 a`, the law `2d dd/a²` on `(0,a]`). Both allocations are
  admissible sign laws and rare, with targets `ρ/2 (1 ± m_K)` and separation
  `ρ/((K+1)(2K+1))`; their odd gap moments agree through depth `2K`, and every
  coin word of length at most `2K` has the same probability under them. The
  last conjunct, that the separation is at most the cap-`2K` diameter
  `CapIdentification.capDiameter`, is a Lean-only consequence, not a claim of
  the source.
* `DepthCapFloorStatement`: `thm:cap`, self-contained. Every population
  procedure obeying the per-coin cap `2K`, with arbitrary pilots, interleaving
  and cross-coin feedback, has the same joint law of seed and full observed
  transcript under the explicit pair (stronger than the source's equality of
  finite-prefix laws, and with no almost-sure termination hypothesis), and its
  worst RMS error is at least `ρ/(2(K+1)(2K+1))`, whatever its expected work,
  both over the pair and through the rare-prior risk `RareAboveTwo.rareRisk`.

The hypotheses `0 < a < 1/2`, `0 < ρ ≤ 1/4` and `K ≥ 1` are those of the
source. The depth-tail bound `thm:tail` is not stated here. -/

noncomputable section
namespace ThresholdHC.DepthLegendre
open MeasureTheory Polynomial
open scoped ENNReal
open ThresholdHC.Tier6 (Gap SignLaw signMean AdaptiveEstimator experimentLaw rootMeanRisk
  populationOutput)
open ThresholdHC.RareAboveTwo (ExactPowerLaw RarePrior rareRisk)
open ThresholdHC.CapIdentification (OddMomentMatch capDiameter)
open ThresholdHC.DepthObstruction (PerCoinCap)
open ThresholdHC.CriticalEntropy (populationWordLikelihood)
open ThresholdHC.ObservableSimulation (gapParameter signUnit)

/-- Rodrigues: `P_n = (2^n n!)⁻¹ dⁿ/dxⁿ (x²-1)ⁿ`. -/
def legendre (n : ℕ) : ℝ[X] :=
  C ((2 ^ n * (n.factorial : ℝ))⁻¹) * derivative^[n] ((X ^ 2 - 1 : ℝ[X]) ^ n)

/-- `c = P'_{2K+1}(0)`. -/
def depthSlope (K : ℕ) : ℝ := (legendre (2*K+1)).derivative.eval 0

/-- `u_K = P_{2K+1}/(c x)`, written as `c⁻¹ · divX P_{2K+1}`. -/
def depthPolynomial (K : ℕ) : ℝ[X] := C (depthSlope K)⁻¹ * (legendre (2*K+1)).divX

/-- `m_K = 1/((K+1)(2K+1))`. -/
def depthMoment (K : ℕ) : ℝ := 1 / (((K:ℝ)+1) * (2*(K:ℝ)+1))

/-- `q_±(d) = (1 ± u_K(d/h))/2 · 1{d ≤ h}`, `h = a√ρ`. -/
def depthSign (K : ℕ) (a ρ : ℝ) (plus : Bool) (d : Gap) : ℝ :=
  if (d:ℝ) ≤ a * Real.sqrt ρ then
    (1 + (if plus then (1:ℝ) else -1) * (depthPolynomial K).eval ((d:ℝ) / (a * Real.sqrt ρ))) / 2
  else 0

/-- proof-body.tex, `lem:poly` (lines 20-34): `u_K` is an even polynomial of degree
`2K`, bounded by one on `[0,1]`, orthogonal to `x^(2j+2)` for `j < K`, with
`∫₀¹ 2x u_K = m_K`. -/
def DepthPolynomialStatement : Prop :=
  ∀ K : ℕ, 1 ≤ K →
    depthSlope K ≠ 0 ∧
    (∀ x : ℝ, x ≠ 0 →
      (depthPolynomial K).eval x = (legendre (2*K+1)).eval x / (depthSlope K * x)) ∧
    (depthPolynomial K).eval 0 = 1 ∧
    (depthPolynomial K).natDegree = 2*K ∧
    (∀ x : ℝ, (depthPolynomial K).eval (-x) = (depthPolynomial K).eval x) ∧
    (∀ x ∈ Set.Icc (0:ℝ) 1, |(depthPolynomial K).eval x| ≤ 1) ∧
    (∀ j < K, ∫ x in (0:ℝ)..1, x^(2*j+2) * (depthPolynomial K).eval x = 0) ∧
    ∫ x in (0:ℝ)..1, 2*x*(depthPolynomial K).eval x = depthMoment K

/-- proof-body.tex, `thm:cap` (lines 89-97, 110-128), the pair: admissible, rare, targets
`ρ/2 (1 ± m_K)`, separation `Δ_K`, matching odd moments and equal word probabilities
through depth `2K`. The `capDiameter` conjunct is a Lean-only consequence. -/
def DepthPairStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (a ρ : ℝ) (K : ℕ),
    0 < a → a < 1/2 → 0 < ρ → ρ ≤ 1/4 → 1 ≤ K → ExactPowerLaw μ 2 a →
    ∃ qH qL : SignLaw, qH.val = depthSign K a ρ true ∧ qL.val = depthSign K a ρ false ∧
      RarePrior μ ρ qH ∧ RarePrior μ ρ qL ∧
      signMean μ qH.val = ρ/2 * (1 + depthMoment K) ∧
      signMean μ qL.val = ρ/2 * (1 - depthMoment K) ∧
      signMean μ qH.val - signMean μ qL.val = ρ / (((K:ℝ)+1) * (2*K+1)) ∧
      OddMomentMatch μ qH qL (2*K) ∧
      (∀ n k : ℕ, n ≤ 2*K → k ≤ n →
        populationWordLikelihood μ (gapParameter false) (gapParameter true) (signUnit qH) n k =
          populationWordLikelihood μ (gapParameter false) (gapParameter true) (signUnit qL) n k) ∧
      ρ / (((K:ℝ)+1) * (2*K+1)) ≤ capDiameter μ ρ (2*K)

/-- proof-body.tex, `thm:cap` (lines 87-151), self-contained: with the explicit pair
inside the existential, arbitrary feedback under per-coin cap `2K` has equal
seed-and-transcript laws and RMS at least `Δ_K/2`, whatever its work. -/
def DepthCapFloorStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (a ρ : ℝ) (K : ℕ) (A : AdaptiveEstimator R),
    0 < a → a < 1/2 → 0 < ρ → ρ ≤ 1/4 → 1 ≤ K → ExactPowerLaw μ 2 a → PerCoinCap A (2*K) →
    (∃ qH qL : SignLaw, qH.val = depthSign K a ρ true ∧ qL.val = depthSign K a ρ false ∧
      RarePrior μ ρ qH ∧ RarePrior μ ρ qL ∧
      (experimentLaw μ A qH).map (fun z => (z.1.1, z.2)) =
        (experimentLaw μ A qL).map (fun z => (z.1.1, z.2)) ∧
      ENNReal.ofReal (ρ / (2*((K:ℝ)+1)*(2*K+1))) ≤
        max (rootMeanRisk (experimentLaw μ A qH) (populationOutput A) (signMean μ qH.val))
            (rootMeanRisk (experimentLaw μ A qL) (populationOutput A) (signMean μ qL.val))) ∧
    ENNReal.ofReal (ρ / (2*((K:ℝ)+1)*(2*K+1))) ≤ rareRisk μ A ρ

end ThresholdHC.DepthLegendre
