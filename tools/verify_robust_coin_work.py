"""Audit the work bounds of the race for a coin with a larger gap than the reference.

Every theorem of the module is restated in full, so a changed hypothesis or
constant is an elaboration error, and the transitive axioms of every
declaration are reported. A declaration in the module that is not registered
here is an error. Prints the kernel report; writes nothing.
"""

import subprocess
from verify_blind_upper_components import (DECLARATION, FORBIDDEN, LEAN, strip_comments,
                                           validate_reports)

MODULE = "ThresholdHC.RobustContinuation.RobustCoinWork"
SOURCE = LEAN / "ThresholdHC/RobustContinuation/RobustCoinWork.lean"
NAMES = [
    "ordinaryWorkKernel_antitone_gap", "race_work_le_ordinary_of_le",
    "negativeReferenceDrift_mono", "negative_scoreStop_work_of_le",
    "bank_race_negative_work_of_le", "prefixMean_mono", "positive_race_survival_of_le",
    "positive_raceRounds_work_of_le", "bank_race_positive_work_of_le",
]


def declared_names():
    """Every declaration of the module, after rejecting proof escapes."""
    source = strip_comments(SOURCE.read_text(encoding="utf-8"))
    if FORBIDDEN.search(source):
        raise ValueError("Forbidden proof escape in " + SOURCE.name)
    return DECLARATION.findall(source)


def audit_input():
    if sorted(declared_names()) != sorted(NAMES):
        raise ValueError("Unregistered or missing robust-work declaration")
    source = """
import ThresholdHC.RobustContinuation.RobustCoinWork
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Set Real
open scoped ENNReal NNReal BigOperators
open ThresholdHC.RobustContinuation
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.Uniform713 ThresholdHC.BlindUpper ThresholdHC.EntropyTailUpper

example : ∀ {M : ℝ} (hM : 0 < M) {d d' : Gap} (h : (d:ℝ) ≤ d'),
    ordinaryWorkKernel M (d':ℝ) ≤ ordinaryWorkKernel M (d:ℝ) := @ordinaryWorkKernel_antitone_gap
example : ∀ (neg pos : PrefixTest) (L : ℕ) (s : Bool) {d₀ d : Gap} (h : (d₀:ℝ) ≤ d),
    (∫ ω, (raceCost neg pos L ω : ℝ) ∂tapeMeasure (gapParameter s d)) ≤
      2*ordinaryWorkKernel (cap L) (d₀:ℝ) := @race_work_le_ordinary_of_le
example : ∀ {d d' r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) (h : d ≤ d'),
    negativeReferenceDrift d r ≤ negativeReferenceDrift d' r := @negativeReferenceDrift_mono
example : ∀ {d₀ d : Gap} (h : (d₀:ℝ) ≤ d) {r b : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) (hdr : (d₀:ℝ)/2 ≤ r) (hrd : r ≤ (d₀:ℝ)) (hb : 0 ≤ b) (M : ℕ),
    (∫ ω, (scoreStop (negativeBitScore r) b M ω : ℝ) ∂tapeMeasure (gapParameter false d)) ≤
      (3/(4*(d₀:ℝ)^2))*(1+b) := @negative_scoreStop_work_of_le
example : ∀ (μ : Measure Gap) (weights : ℕ → ℝ≥0) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (u : ℝ) (j L : ℕ) (hw : 0 < (weights j:ℝ)) (hw1 : (weights j:ℝ) ≤ 1) {d₀ d : Gap} (hd : d₀ ∈ EntropyTailQuantile.band j) (h : (d₀:ℝ) ≤ d),
    (∫ ω, (raceCost (negativeBankTest weights ε) (positiveBankTest μ weights u) L ω : ℝ)
      ∂tapeMeasure (gapParameter false d)) ≤
      (3/(2*(d₀:ℝ)^2))*(1+log (ε*(weights j:ℝ))⁻¹) := @bank_race_negative_work_of_le
example : ∀ (n : ℕ) {ω ω' : ℕ → Bool} (h : ω ≤ ω'),
    prefixMean observations n ω ≤ prefixMean observations n ω' := @prefixMean_mono
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (weights : ℕ → ℝ≥0) (ε : ℝ) {u V U : ℝ} (hu : 0 ≤ u) (j L : ℕ) {d₀ d : Gap} (hd : d₀ ∈ EntropyTailQuantile.band j) (h : (d₀:ℝ) ≤ d) {n : ℕ} (hn : 0 < n) (hU : U ≤ n*(d₀:ℝ)^2/3) (hLap : nullLaplace μ n ≤ V) (hV : V ≤ u*(weights j:ℝ)*exp U),
    (tapeMeasure (gapParameter true d)).real
      {ω | n < raceRounds (negativeBankTest weights ε) (positiveBankTest μ weights u) L ω} ≤
      exp (-(n:ℝ)*(d₀:ℝ)^2/2) := @positive_race_survival_of_le
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (weights : ℕ → ℝ≥0) (ε : ℝ) {u V U : ℝ} (hu : 0 ≤ u) (hU : 1 ≤ U) (j L : ℕ) {d₀ d : Gap} (hd : d₀ ∈ EntropyTailQuantile.band j) (h : (d₀:ℝ) ≤ d) (hLap : ∀ n : ℕ, 1 ≤ n*(d₀:ℝ)^2 → nullLaplace μ n ≤ V) (hV : V ≤ u*(weights j:ℝ)*exp U),
    (∫ ω, (raceRounds (negativeBankTest weights ε) (positiveBankTest μ weights u) L ω : ℝ)
      ∂tapeMeasure (gapParameter true d)) ≤ 6*U/(d₀:ℝ)^2 := @positive_raceRounds_work_of_le
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] (hσ : Integrable (fun x : Gap => (x:ℝ)⁻¹^2) σ) (hτ : Integrable (fun x : Gap => (x:ℝ)⁻¹) τ) (weights : ℕ → ℝ≥0) {ε ρ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ) (j L : ℕ) (hw : 0 < (weights j:ℝ)) (hw1 : (weights j:ℝ) ≤ 1) {d₀ d : Gap} (hd : d₀ ∈ EntropyTailQuantile.band j) (h : (d₀:ℝ) ≤ d),
    (∫ ω, (raceCost (negativeBankTest weights ε) (positiveBankTest (σ+τ+ζ) weights (ρ*ε)) L ω : ℝ)
      ∂tapeMeasure (gapParameter true d)) ≤
      12*positiveAllowance ε (weights j:ℝ) ρ (threePieceEnvelope σ τ ζ d₀)/(d₀:ℝ)^2 := @bank_race_positive_work_of_le
"""
    if source.count("example ") != len(NAMES):
        raise ValueError("Each robust-work declaration needs exactly one restated statement")
    roots = {"ThresholdHC.RobustContinuation." + name for name in NAMES}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", MODULE], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "-j1", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {source.count('example ')} exact statements and {len(roots)} transitive reports")


if __name__ == "__main__":
    main()
