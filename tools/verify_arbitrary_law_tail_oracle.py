"""Audit the oracle comparison of the arbitrary-law tail certificate.

Every definition and theorem of the two tail-oracle modules is restated in
full, so a changed definition, hypothesis or constant is an elaboration error,
and the transitive axioms of every declaration are reported. A declaration in
those modules that is not registered here is an error. Prints the kernel
report; writes nothing.
"""

import subprocess
from verify_blind_upper_components import (DECLARATION, FORBIDDEN, LEAN, strip_comments,
                                           validate_reports)

MODULE = "ThresholdHC.ArbitraryLawAdaptation.TailOracleLaw"
SOURCES = [LEAN / "ThresholdHC/ArbitraryLawAdaptation" / (name + ".lean")
           for name in ("TailOracle", "TailOracleLaw")]
NAMES = [
    "tailOracleKernel", "TailOnset", "half_pow_eq", "four_pow_eq", "one_add_logb_two_le",
    "tailWorkEnvelope_div_le", "tailUnresolvedProb_le_four_min", "tailOracleKernel_le_tail",
    "tailLog_le", "tailOracleKernel_le_core", "tailOracleKernel_nonneg", "tailOracleKernel_le_two",
    "measurable_tailOracleKernel", "integrable_tailOracleKernel", "tail_oracle_integral",
    "tail_onset_exists", "tailOnset_eventually", "selection_ge_scale", "tail_oracle_comparison",
    "tail_bound_le_oracle", "original_tail_oracle", "original_tail_oracle_array",
    "original_tail_oracle_eventually", "original_tail_oracle_all_depths",
    "original_tail_oracle_all_depths_array", "original_tail_oracle_all_depths_eventually",
]


def declared_names():
    """Every declaration of the two modules, after rejecting proof escapes."""
    found = []
    for path in SOURCES:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + path.name)
        found += DECLARATION.findall(source)
    return found


def audit_input():
    if sorted(declared_names()) != sorted(NAMES):
        raise ValueError("Unregistered or missing tail-oracle declaration")
    source = """
import ThresholdHC.ArbitraryLawAdaptation.TailOracleLaw
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Real ProbabilityTheory
open scoped ENNReal
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.Tier2 ThresholdHC.Tier6
open ThresholdHC.Uniform713 ThresholdHC.EntropyTailUpper ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.EntropyTailQuantile

example : ∀ (J : ℕ) (d : Gap), tailOracleKernel J d =
    tailUnresolvedProb J d + tailWorkEnvelope J d / 4 ^ J := fun _ _ => rfl
example : ∀ (μ : Measure Gap) (ρ : ℝ) (J : ℕ), TailOnset μ ρ J ↔
    2048 * ((J : ℝ) + 1) * (1 / 2) ^ J / (quantileThreshold μ ρ) ^ 2 ≤ Real.sqrt ρ :=
  fun _ _ _ => Iff.rfl

example : ∀ (J : ℕ),
    (1 / 2 : ℝ) ^ J = 1 / 2 ^ J := @half_pow_eq
example : ∀ (J : ℕ),
    (4 : ℝ) ^ J = (2 ^ J) ^ 2 := @four_pow_eq
example : ∀ {x : ℝ} (hx : 1 ≤ x),
    1 + Real.logb 2 x ≤ 2 * x := @one_add_logb_two_le
example : ∀ (J : ℕ) (d : Gap),
    tailWorkEnvelope J d / 4 ^ J ≤ 2048 * min 1 ((1 / 2) ^ J / (d : ℝ)) := @tailWorkEnvelope_div_le
example : ∀ (J : ℕ) (d : Gap),
    tailUnresolvedProb J d ≤ 4 * min 1 ((1 / 2) ^ J / (d : ℝ)) := @tailUnresolvedProb_le_four_min
example : ∀ (J : ℕ) (d : Gap),
    tailOracleKernel J d ≤ 2052 * min 1 ((1 / 2) ^ J / (d : ℝ)) := @tailOracleKernel_le_tail
example : ∀ (J : ℕ) (d : Gap),
    tailLog J d ≤ J := @tailLog_le
example : ∀ (J : ℕ) {a : ℝ} (ha : 0 < a) (d : Gap) (had : a ≤ (d : ℝ)),
    tailOracleKernel J d ≤ (1024 * ((J : ℝ) + 1) + 16) * ((1 / 2) ^ J) ^ 2 / a ^ 2 := @tailOracleKernel_le_core
example : ∀ (J : ℕ) (d : Gap),
    0 ≤ tailOracleKernel J d := @tailOracleKernel_nonneg
example : ∀ (J : ℕ) (d : Gap),
    tailOracleKernel J d ≤ 2 := @tailOracleKernel_le_two
example : ∀ (J : ℕ),
    Measurable (tailOracleKernel J) := @measurable_tailOracleKernel
example : ∀ (ξ : Measure Gap) [IsFiniteMeasure ξ] (J : ℕ),
    Integrable (tailOracleKernel J) ξ := @integrable_tailOracleKernel
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (J : ℕ),
    tailUnresolvedMass μ J + (∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J =
      ∫ d, tailOracleKernel J d ∂μ := @tail_oracle_integral
example : ∀ {a ρ : ℝ} (ha : 0 < a) (hρ : 0 < ρ),
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      2048 * ((J : ℝ) + 1) * (1 / 2) ^ J / a ^ 2 ≤ Real.sqrt ρ := @tail_onset_exists
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1),
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → TailOnset μ ρ J := @tailOnset_eventually
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (J : ℕ) (hsmall : 2 * (1 / 2 : ℝ) ^ J ≤ Real.sqrt ρ),
    ENNReal.ofReal (2 * (1 / 2) ^ J * Real.sqrt ρ) ≤ ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) := @selection_ge_scale
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (J : ℕ) (hon : TailOnset μ ρ J),
    ENNReal.ofReal (tailUnresolvedMass μ J + (∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J) ≤
      4096 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) := @tail_oracle_comparison
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (J : ℕ) (hon : TailOnset μ ρ J),
    ENNReal.ofReal (min 1 (128 * max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J))) ≤
      524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J) := @tail_bound_le_oracle
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (J m : ℕ) (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) (hmδ : 8 * log (2 / δ) ≤ m) (hon : TailOnset μ ρ J),
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))).real
      {ω | (∀ b' M' : ℕ → ℕ,
      μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J m b' M' ω) ∧
      ENNReal.ofReal (medianUpper J m (fun _ => 4 ^ J) (fun _ => 4 ^ J) ω) ≤
      524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)} := @original_tail_oracle
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (J m : ℕ) (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) (hmδ : 8 * log (2 / δ) ≤ m) (hon : TailOnset μ ρ J),
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      medianUpper J m b' M' (fun j i => ω (Nat.pair j i))) ∧
      ENNReal.ofReal (medianUpper J m (fun _ => 4 ^ J) (fun _ => 4 ^ J)
      (fun j i => ω (Nat.pair j i))) ≤
      524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)} := @original_tail_oracle_array
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4),
    ∃ J₀ : ℕ, ∀ (J m : ℕ) (δ : ℝ), J₀ ≤ J → 0 < m → 0 < δ → 8 * log (2 / δ) ≤ m →
      1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      medianUpper J m b' M' (fun j i => ω (Nat.pair j i))) ∧
      ENNReal.ofReal (medianUpper J m (fun _ => 4 ^ J) (fun _ => 4 ^ J)
      (fun j i => ω (Nat.pair j i))) ≤
      524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J)} := @original_tail_oracle_eventually
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (m : ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ) (hm : ∀ J : ℕ, 1 ≤ J → 0 < m J) (hmδ : ∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J),
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))).real
      {ω | ∀ J, 1 ≤ J →
      (∀ b' M' : ℕ → ℕ,
      μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J (m J) b' M' (ω J)) ∧
      (TailOnset μ ρ J →
      ENNReal.ofReal (medianUpper J (m J) (fun _ => 4 ^ J) (fun _ => 4 ^ J) (ω J)) ≤
      524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J))} := @original_tail_oracle_all_depths
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (m : ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ) (hm : ∀ J : ℕ, 1 ≤ J → 0 < m J) (hmδ : ∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J),
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | ∀ J, 1 ≤ J →
      (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      medianUpper J (m J) b' M' (fun j i => ω (Nat.pair J (Nat.pair j i)))) ∧
      (TailOnset μ ρ J →
      ENNReal.ofReal (medianUpper J (m J) (fun _ => 4 ^ J) (fun _ => 4 ^ J)
      (fun j i => ω (Nat.pair J (Nat.pair j i)))) ≤
      524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J))} := @original_tail_oracle_all_depths_array
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4),
    ∃ J₀ : ℕ, ∀ (m : ℕ → ℕ) (δ : ℝ), 0 < δ → (∀ J : ℕ, 1 ≤ J → 0 < m J) →
      (∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J) →
      1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | ∀ J, 1 ≤ J →
      (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      medianUpper J (m J) b' M' (fun j i => ω (Nat.pair J (Nat.pair j i)))) ∧
      (J₀ ≤ J →
      ENNReal.ofReal (medianUpper J (m J) (fun _ => 4 ^ J) (fun _ => 4 ^ J)
      (fun j i => ω (Nat.pair J (Nat.pair j i)))) ≤
      524288 * ThresholdHC.EntropyTail.selection μ ρ (4 ^ J))} := @original_tail_oracle_all_depths_eventually
"""
    if source.count("example ") != len(NAMES):
        raise ValueError("Each tail-oracle declaration needs exactly one restated statement")
    roots = {"ThresholdHC.ArbitraryLawAdaptation." + name for name in NAMES}
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
