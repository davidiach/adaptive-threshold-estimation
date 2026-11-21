import ThresholdHC.ArbitraryLawAdaptation.LightMultiplier

/-! Target statements for the constant `C_V` of the light random contraction.

Source: `paper/v6/arbitrary-law-adaptation.tex`, subsection
`sec:arbitrary-law-adaptation`, subsubsection *Finite envelopes and the zero
atom*, paragraph *A light random contraction*, display `(UA4)`; the same text is
display `(A4)` of `docs/ARBITRARY_LAW_ADAPTATION.md`. The multiplier `V` has
distribution function `G_V(v) = 2e^{-1/(2v^2)}` on `(0,1/4)` and `G_V = 1` for
`v ≥ 1/4` (the existing `lightCDF`). With `p_k = Pr(2^{-k-1} < V ≤ 2^{-k})`,
`k ≥ 2`, the paper states `p_2 = 1 - 2e^{-32}`, `p_k ≤ 2e^{-4^k/2}` for `k ≥ 3`,
that the `k = 2` summand is less than `192`,
`C_V = Σ_{k≥2} 4^{k+1} p_k [1 + log(1/p_k) + log 2] < 256`,
`E V^{-2} ≤ C_V ≤ 256` and `E V^{-1} ≤ 16`.

Only the constant, the band masses and the moment bounds are stated. The
entropy inequality `Γ_{L(VD)} ≤ C_V Γ_μ` of `(UA4)` is not stated here. The
series is indexed by `k = j+2` and carries an explicit summability conjunct.
Logarithms follow Mathlib's conventions (`log 0 = 0`, `1/0 = 0`); every `p_k`
lies in `[0,1]`. The proofs are in the other modules of this group. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.LightContractionConstant
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.ArbitraryLawAdaptation

/-- `p_k = P(2^{-k-1} < V ≤ 2^{-k})` under the multiplier law `ν`. -/
def bandProb (ν : Measure Gap) (k : ℕ) : ℝ :=
  (ν {v : Gap | (1/2 : ℝ)^(k+1) < (v : ℝ) ∧ (v : ℝ) ≤ (1/2 : ℝ)^k}).toReal

/-- The summand `4^{k+1} p_k [1 + log(1/p_k) + log 2]` of `C_V`. -/
def cvTerm (ν : Measure Gap) (k : ℕ) : ℝ :=
  (4 : ℝ)^(k+1) * bandProb ν k * (1 + Real.log (1 / bandProb ν k) + Real.log 2)

/-- `C_V = Σ_{k≥2} cvTerm ν k`, indexed by `k = j+2`. -/
def lightCV (ν : Measure Gap) : ℝ := ∑' j : ℕ, cvTerm ν (j+2)

/-- `p_2 = 1 - 2e^{-32}`. -/
def FirstBandStatement : Prop :=
  ∀ (ν : Measure Gap) [IsProbabilityMeasure ν],
    (∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) →
    bandProb ν 2 = 1 - 2 * Real.exp (-32)

/-- `p_k ≤ 2e^{-4^k/2}` for `k ≥ 3`. -/
def TailBandStatement : Prop :=
  ∀ (ν : Measure Gap) [IsProbabilityMeasure ν],
    (∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) →
    ∀ k : ℕ, 3 ≤ k → bandProb ν k ≤ 2 * Real.exp (-((4 : ℝ)^k / 2))

/-- The `k = 2` summand of `C_V` is less than 192. -/
def FirstTermStatement : Prop :=
  ∀ (ν : Measure Gap) [IsProbabilityMeasure ν],
    (∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) →
    cvTerm ν 2 < 192

/-- The constant of (A4)/(UA4): the series `C_V` converges and `C_V < 256`.
The entropy inequality `Γ_{L(VD)} ≤ C_V Γ_μ` of (A4)/(UA4) is not stated here. -/
def LightCVStatement : Prop :=
  ∀ (ν : Measure Gap) [IsProbabilityMeasure ν],
    (∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) →
    Summable (fun j : ℕ => cvTerm ν (j+2)) ∧ lightCV ν < 256

/-- `E V^{-2} ≤ C_V`, `E V^{-2} ≤ 256` and `E V^{-1} ≤ 16`; `C_V < 256` is
`LightCVStatement`. -/
def LightMomentStatement : Prop :=
  ∀ (ν : Measure Gap) [IsProbabilityMeasure ν],
    (∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) →
    (∫⁻ v, ENNReal.ofReal (((v : ℝ)⁻¹)^2) ∂ν) ≤ ENNReal.ofReal (lightCV ν) ∧
    (∫⁻ v, ENNReal.ofReal (((v : ℝ)⁻¹)^2) ∂ν) ≤ 256 ∧
    (∫⁻ v, ENNReal.ofReal ((v : ℝ)⁻¹) ∂ν) ≤ 16

/-- For the constructed multiplier `lightMultiplier`: `p_2 = 1 - 2e^{-32}`, the
series converges and `C_V < 256`. -/
def ConstructedLightCVStatement : Prop :=
  bandProb lightMultiplier 2 = 1 - 2 * Real.exp (-32) ∧
  Summable (fun j : ℕ => cvTerm lightMultiplier (j+2)) ∧ lightCV lightMultiplier < 256

end ThresholdHC.LightContractionConstant
