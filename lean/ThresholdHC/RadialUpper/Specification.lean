import ThresholdHC.ConfidenceTransfer.CriticalModel
import ThresholdHC.EntropyTailExecution.CallMachine

/-!
# The calibrated radial upper bound on the known radial submodel

Source: `research/2026-10-27-population-step/lower/population_information.tex`,
Corollary `pop:radial-upper` (with its proof), on the known radial submodel
defined before Proposition `pop:radial-information` in the same file
(the subsection on the radial path).
The fixed range `0 < rho <= 1/4` and the quadratic law with `a = 1/4` are those of
`research/2026-10-27-population-step/lower/proof.tex` (lines 12-13).

The hidden gap law is the exact quadratic law `criticalPositiveLaw` (density `32d`
on `(0,1/4]`). For a cutoff `b`, the radial profile is `w_b(d) = min 1 (b^2/d^2)`
and the submodel is `q_eta = (1+eta) w_b / 2` with `|eta| <= 1/2`. The cutoff is
calibrated by `E w_b(D) = rho` (`RadialCalibrated`); `RadialCutoffStatement` states
(and `radial_cutoff` proves) that the calibrated cutoff exists and is unique, so the
other statements are not vacuous. The ideal arithmetic convention of the source (exact evaluation of known
one-dimensional calibration integrals) is modelled by real constants in the
estimator.

* `RadialCallStatement`: one capped observable call on a fresh coin, unbiased for
  `theta(q_eta)`, with variance at most `(11/2) rho L` and expected flips below `29`
  uniformly in `eta`, where `L = 1 + log(1/rho)`.
* `RadialUpperStatement`: Corollary `pop:radial-upper`, an observable estimator with
  expected work at most `B` and RMS at most `min(rho/4, sqrt(160 rho L/B))` for every
  `q_eta`. The guarantee is only over the submodel, as in the source.
* `RadialMinimaxUpperStatement`: the same bound for the submodel minimax risk.
-/

noncomputable section
namespace ThresholdHC.RadialUpper
open MeasureTheory ThresholdHC.Tier6
open ThresholdHC.ConfidenceTransfer (criticalPositiveLaw)
open ThresholdHC.ObservableSimulation (originalPopulationTapeLaw)
open scoped ENNReal

/-- The radial profile `w_b(d) = min(1, b^2/d^2)` on the hidden-gap domain. -/
def radialWeight (b : ℝ) (d : Gap) : ℝ := min 1 (b^2/(d:ℝ)^2)

/-- The submodel index `eta` with `|eta| <= 1/2`. -/
abbrev RadialIndex := Set.Icc (-(1/2) : ℝ) (1/2)

/-- The radial sign law `q_eta = (1+eta) w_b / 2`. -/
def radialSign (b : ℝ) (η : RadialIndex) : SignLaw :=
  ⟨fun d => (1+(η:ℝ))/2 * radialWeight b d,
    by unfold radialWeight; fun_prop,
    fun d => by
      have h := η.2
      have hw0 : 0 ≤ radialWeight b d := le_min zero_le_one (by positivity)
      have hw1 : radialWeight b d ≤ 1 := min_le_left _ _
      constructor <;> nlinarith [h.1, h.2]⟩

/-- The rarity factor `L = 1 + log(1/rho)`. -/
def radialLogFactor (ρ : ℝ) : ℝ := 1 + Real.log (1/ρ)

/-- `b` is the rarity-calibrated cutoff: `E w_b(D) = rho` under the quadratic law. -/
def RadialCalibrated (ρ b : ℝ) : Prop :=
  0 < b ∧ b < 1/4 ∧ signMean criticalPositiveLaw (radialWeight b) = ρ

/-- Nonvacuity companion: the calibrated cutoff exists and is unique. -/
def RadialCutoffStatement : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1/4 → ∃! b : ℝ, RadialCalibrated ρ b

/-- The one-coin constants of the proof of Corollary `pop:radial-upper`: one capped
observable call on a fresh coin, bounded, unbiased for `theta(q_eta)`, with variance
at most `(11/2) rho L` and expected flips below `29`, uniformly in `eta`. -/
def RadialCallStatement : Prop :=
  ∀ ρ b : ℝ, 0 < ρ → ρ ≤ 1/4 → RadialCalibrated ρ b →
    ∃ (Y : EntropyTailExecution.FiniteCall) (N : ℕ) (U : ℝ),
      (∀ ω, Y.cost ω ≤ N) ∧ (∀ ω, |Y.value ω| ≤ U) ∧
      ∀ η : RadialIndex,
        (∫ ω, (Y.cost ω : ℝ) ∂originalPopulationTapeLaw criticalPositiveLaw (radialSign b η)) < 29 ∧
        (∫ ω, Y.value ω ∂originalPopulationTapeLaw criticalPositiveLaw (radialSign b η)) =
          signMean criticalPositiveLaw (radialSign b η).val ∧
        (∫ ω, (Y.value ω)^2 ∂originalPopulationTapeLaw criticalPositiveLaw (radialSign b η)) -
          (∫ ω, Y.value ω ∂originalPopulationTapeLaw criticalPositiveLaw (radialSign b η))^2 ≤
            11/2*ρ*radialLogFactor ρ

/-- Corollary `pop:radial-upper`, algorithmic form. -/
def RadialUpperStatement : Prop :=
  ∀ ρ b B : ℝ, 0 < ρ → ρ ≤ 1/4 → RadialCalibrated ρ b → 0 < B →
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      (∀ η : RadialIndex,
        expectedWork criticalPositiveLaw A (radialSign b η) ≤ ENNReal.ofReal B) ∧
      ∀ η : RadialIndex,
        rootMeanRisk (experimentLaw criticalPositiveLaw A (radialSign b η)) (populationOutput A)
            (signMean criticalPositiveLaw (radialSign b η).val) ≤
          ENNReal.ofReal (min (ρ/4) (Real.sqrt (160*ρ*radialLogFactor ρ/B)))

/-- `R_radial(B)`: the minimax RMS over the submodel with uniform submodel budget `B`. -/
def radialMinimaxRisk (b B : ℝ) : ℝ≥0∞ :=
  sInf {r | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    (∀ η : RadialIndex, expectedWork criticalPositiveLaw A (radialSign b η) ≤ ENNReal.ofReal B) ∧
    r = ⨆ η : RadialIndex, rootMeanRisk (experimentLaw criticalPositiveLaw A (radialSign b η))
          (populationOutput A) (signMean criticalPositiveLaw (radialSign b η).val)}

/-- Corollary `pop:radial-upper`, minimax form: `R_radial(B) <= min(rho/4, sqrt(160 rho L/B))`. -/
def RadialMinimaxUpperStatement : Prop :=
  ∀ ρ b B : ℝ, 0 < ρ → ρ ≤ 1/4 → RadialCalibrated ρ b → 0 < B →
    radialMinimaxRisk b B ≤ ENNReal.ofReal (min (ρ/4) (Real.sqrt (160*ρ*radialLogFactor ρ/B)))

end ThresholdHC.RadialUpper
