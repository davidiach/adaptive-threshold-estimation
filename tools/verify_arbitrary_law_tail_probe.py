"""Audit the capped tail probe of the arbitrary-law tail certificate.

Every definition and theorem of the three tail-probe modules is restated in
full, so a changed definition, hypothesis or constant is an elaboration error,
and the transitive axioms of every declaration are reported. A declaration in
those modules that is not registered here is an error. Prints the kernel
report; writes nothing.
"""

import subprocess
from verify_blind_upper_components import (DECLARATION, FORBIDDEN, LEAN, strip_comments,
                                           validate_reports)

MODULE = "ThresholdHC.ArbitraryLawAdaptation.TailProbeLaw"
SOURCES = [LEAN / "ThresholdHC/ArbitraryLawAdaptation" / (name + ".lean")
           for name in ("TailProbe", "TailProbeProbability", "TailProbeLaw")]
NAMES = [
    "probeWork", "probeAdmits", "probeHorizon", "probeReaches", "probeCompleted", "probeFlips",
    "probeUnresolved", "probeUpper", "probeWork_zero", "probeWork_succ", "probeWork_mono",
    "le_probeWork", "probeWork_le", "probeWork_strictMono", "probeWork_congr", "probeAdmits_zero",
    "probeAdmits_of_le", "probeReaches_zero", "probeReaches_of_le", "bddAbove_probeAdmits",
    "bddAbove_probeReaches", "le_probeHorizon_iff", "le_probeCompleted_iff", "probeHorizon_admits",
    "probeCompleted_reaches", "probeHorizon_le", "probeHorizon_unresolved",
    "probeCompleted_le_horizon", "probeCompleted_le_cap", "probeWork_completed_le",
    "probeCompleted_le_budget", "probeCompleted_mono", "probeCompleted_cap_inactive",
    "probeFlips_le", "probeFlips_le_cap", "probeWork_completed_le_flips", "probeFlips_of_stopped",
    "probeFlips_of_running", "probeFlips_mono", "probe_congr", "probeUpper_zero", "probeUpper_pos",
    "probeUpper_le_one", "probeUpper_le_div", "probeUpper_antitone", "measurable_probeWork",
    "measurable_streamUnresolved", "measurableSet_probeAdmits", "measurableSet_probeReaches",
    "measurable_probeCompleted", "measurableSet_probeValid", "stream_eval_real",
    "stream_eval_integral", "stream_all_resolved", "stream_some_unresolved_le",
    "integrable_probeWork", "stream_expected_work", "stream_work_exceeds_le",
    "resolved_prefix_of_upper_lt", "exp_neg_three_le", "stream_probe_invalid_le",
    "stream_probe_valid", "stream_probe_performance", "originalSimulationLaw_coins",
    "one_le_tailWorkEnvelope", "one_le_tailWorkEnvelope_integral", "original_probe_valid",
    "original_probe_performance", "original_probe_performance_uncapped",
]


def declared_names():
    """Every declaration of the three modules, after rejecting proof escapes."""
    found = []
    for path in SOURCES:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + path.name)
        found += DECLARATION.findall(source)
    return found


def audit_input():
    if sorted(declared_names()) != sorted(NAMES):
        raise ValueError("Unregistered or missing tail-probe declaration")
    source = """
import ThresholdHC.ArbitraryLawAdaptation.TailProbeLaw
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Real ProbabilityTheory
open scoped ENNReal
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.Tier2 ThresholdHC.Tier6
open ThresholdHC.Uniform713 ThresholdHC.EntropyTailUpper ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation

example : ∀ (J : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ),
    probeWork J ω n = ∑ i ∈ Finset.range n, tailWork J (ω i) := fun _ _ _ => rfl
example : ∀ (J M : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ), probeAdmits J M ω n ↔
    n ≤ M ∧ ∀ i, i + 1 < n → ¬ tailUnresolved J (ω i) := fun _ _ _ _ => Iff.rfl
example : ∀ (J M : ℕ) (ω : ℕ → ℕ → Bool),
    probeHorizon J M ω = sSup {n | probeAdmits J M ω n} := fun _ _ _ => rfl
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ), probeReaches J b M ω n ↔
    probeAdmits J M ω n ∧ probeWork J ω n ≤ b := fun _ _ _ _ _ => Iff.rfl
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeCompleted J b M ω = sSup {n | probeReaches J b M ω n} := fun _ _ _ _ => rfl
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeFlips J b M ω = min b (probeWork J ω (probeHorizon J M ω)) := fun _ _ _ _ => rfl
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool), probeUnresolved J b M ω ↔
    0 < probeCompleted J b M ω ∧ tailUnresolved J (ω (probeCompleted J b M ω - 1)) :=
  fun _ _ _ _ => Iff.rfl
example : ∀ n : ℕ, probeUpper n = if n = 0 then (1 : ℝ) else min 1 (8 / (n : ℝ)) :=
  fun _ => rfl

example : ∀ (J : ℕ) (ω : ℕ → ℕ → Bool),
    probeWork J ω 0 = 0 := @probeWork_zero
example : ∀ (J : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ),
    probeWork J ω (n + 1) = probeWork J ω n + tailWork J (ω n) := @probeWork_succ
example : ∀ (J : ℕ) (ω : ℕ → ℕ → Bool) {n n' : ℕ} (h : n ≤ n'),
    probeWork J ω n ≤ probeWork J ω n' := @probeWork_mono
example : ∀ (J : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ),
    n ≤ probeWork J ω n := @le_probeWork
example : ∀ (J : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ),
    probeWork J ω n ≤ n * 4 ^ J := @probeWork_le
example : ∀ (J : ℕ) (ω : ℕ → ℕ → Bool) {n n' : ℕ} (h : n < n'),
    probeWork J ω n < probeWork J ω n' := @probeWork_strictMono
example : ∀ {J n : ℕ} {ω ω' : ℕ → ℕ → Bool} (h : ∀ i < n, ∀ k < tailWork J (ω i), ω i k = ω' i k),
    probeWork J ω' n = probeWork J ω n := @probeWork_congr
example : ∀ (J M : ℕ) (ω : ℕ → ℕ → Bool),
    probeAdmits J M ω 0 := @probeAdmits_zero
example : ∀ {J M : ℕ} {ω : ℕ → ℕ → Bool} {n n' : ℕ} (h : probeAdmits J M ω n) (hn : n' ≤ n),
    probeAdmits J M ω n' := @probeAdmits_of_le
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeReaches J b M ω 0 := @probeReaches_zero
example : ∀ {J b M : ℕ} {ω : ℕ → ℕ → Bool} {n n' : ℕ} (h : probeReaches J b M ω n) (hn : n' ≤ n),
    probeReaches J b M ω n' := @probeReaches_of_le
example : ∀ (J M : ℕ) (ω : ℕ → ℕ → Bool),
    BddAbove {n | probeAdmits J M ω n} := @bddAbove_probeAdmits
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    BddAbove {n | probeReaches J b M ω n} := @bddAbove_probeReaches
example : ∀ (J M : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ),
    n ≤ probeHorizon J M ω ↔ probeAdmits J M ω n := @le_probeHorizon_iff
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool) (n : ℕ),
    n ≤ probeCompleted J b M ω ↔ probeReaches J b M ω n := @le_probeCompleted_iff
example : ∀ (J M : ℕ) (ω : ℕ → ℕ → Bool),
    probeAdmits J M ω (probeHorizon J M ω) := @probeHorizon_admits
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeReaches J b M ω (probeCompleted J b M ω) := @probeCompleted_reaches
example : ∀ (J M : ℕ) (ω : ℕ → ℕ → Bool),
    probeHorizon J M ω ≤ M := @probeHorizon_le
example : ∀ {J M : ℕ} {ω : ℕ → ℕ → Bool} (h : probeHorizon J M ω < M),
    0 < probeHorizon J M ω ∧ tailUnresolved J (ω (probeHorizon J M ω - 1)) := @probeHorizon_unresolved
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeCompleted J b M ω ≤ probeHorizon J M ω := @probeCompleted_le_horizon
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeCompleted J b M ω ≤ M := @probeCompleted_le_cap
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeWork J ω (probeCompleted J b M ω) ≤ b := @probeWork_completed_le
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeCompleted J b M ω ≤ b := @probeCompleted_le_budget
example : ∀ (J : ℕ) (ω : ℕ → ℕ → Bool) {b b' M M' : ℕ} (hb : b ≤ b') (hM : M ≤ M'),
    probeCompleted J b M ω ≤ probeCompleted J b' M' ω := @probeCompleted_mono
example : ∀ (J : ℕ) (ω : ℕ → ℕ → Bool) {b M : ℕ} (h : b ≤ M),
    probeCompleted J b M ω = probeCompleted J b b ω := @probeCompleted_cap_inactive
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeFlips J b M ω ≤ b := @probeFlips_le
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeFlips J b M ω ≤ M * 4 ^ J := @probeFlips_le_cap
example : ∀ (J b M : ℕ) (ω : ℕ → ℕ → Bool),
    probeWork J ω (probeCompleted J b M ω) ≤ probeFlips J b M ω := @probeWork_completed_le_flips
example : ∀ {J b M : ℕ} {ω : ℕ → ℕ → Bool} (h : probeCompleted J b M ω = probeHorizon J M ω),
    probeFlips J b M ω = probeWork J ω (probeCompleted J b M ω) := @probeFlips_of_stopped
example : ∀ {J b M : ℕ} {ω : ℕ → ℕ → Bool} (h : probeCompleted J b M ω < probeHorizon J M ω),
    probeFlips J b M ω = b ∧ b < probeWork J ω (probeCompleted J b M ω + 1) := @probeFlips_of_running
example : ∀ (J M : ℕ) (ω : ℕ → ℕ → Bool) {b b' : ℕ} (h : b ≤ b'),
    probeFlips J b M ω ≤ probeFlips J b' M ω := @probeFlips_mono
example : ∀ {J b M : ℕ} {ω ω' : ℕ → ℕ → Bool} (h : ∀ i k, k < tailWork J (ω i) → probeWork J ω i + k < probeFlips J b M ω → ω i k = ω' i k),
    probeCompleted J b M ω' = probeCompleted J b M ω ∧
      probeFlips J b M ω' = probeFlips J b M ω ∧
      (probeUnresolved J b M ω' ↔ probeUnresolved J b M ω) := @probe_congr
example :
    probeUpper 0 = 1 := @probeUpper_zero
example : ∀ (n : ℕ),
    0 < probeUpper n := @probeUpper_pos
example : ∀ (n : ℕ),
    probeUpper n ≤ 1 := @probeUpper_le_one
example : ∀ {n : ℕ} (h : 0 < n),
    probeUpper n ≤ 8 / n := @probeUpper_le_div
example : ∀ {n n' : ℕ} (h : n ≤ n'),
    probeUpper n' ≤ probeUpper n := @probeUpper_antitone
example : ∀ (J n : ℕ),
    Measurable (fun ω : ℕ → ℕ → Bool => probeWork J ω n) := @measurable_probeWork
example : ∀ (J i : ℕ),
    Measurable (fun ω : ℕ → ℕ → Bool => tailUnresolved J (ω i)) := @measurable_streamUnresolved
example : ∀ (J M n : ℕ),
    MeasurableSet {ω : ℕ → ℕ → Bool | probeAdmits J M ω n} := @measurableSet_probeAdmits
example : ∀ (J b M n : ℕ),
    MeasurableSet {ω : ℕ → ℕ → Bool | probeReaches J b M ω n} := @measurableSet_probeReaches
example : ∀ (J b M : ℕ),
    Measurable (probeCompleted J b M) := @measurable_probeCompleted
example : ∀ (J : ℕ) (F : ℝ),
    MeasurableSet {ω : ℕ → ℕ → Bool | ∀ b M, F ≤ probeUpper (probeCompleted J b M ω)} := @measurableSet_probeValid
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (i : ℕ) {S : Set (ℕ → Bool)} (hS : MeasurableSet S),
    (Measure.infinitePi (fun _ : ℕ => ν)).real {ω | ω i ∈ S} = ν.real S := @stream_eval_real
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (i : ℕ) (G : (ℕ → Bool) → ℝ) (hG : Measurable G),
    ∫ ω, G (ω i) ∂Measure.infinitePi (fun _ : ℕ => ν) = ∫ t, G t ∂ν := @stream_eval_integral
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (J m : ℕ),
    (Measure.infinitePi (fun _ : ℕ => ν)).real {ω | ∀ i < m, ¬ tailUnresolved J (ω i)} =
      (1 - ν.real {t | tailUnresolved J t}) ^ m := @stream_all_resolved
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (J q : ℕ),
    (Measure.infinitePi (fun _ : ℕ => ν)).real {ω | ∃ i < q, tailUnresolved J (ω i)} ≤
      q * ν.real {t | tailUnresolved J t} := @stream_some_unresolved_le
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (J q : ℕ),
    Integrable (fun ω : ℕ → ℕ → Bool => (probeWork J ω q : ℝ))
      (Measure.infinitePi (fun _ : ℕ => ν)) := @integrable_probeWork
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (J q : ℕ),
    ∫ ω, (probeWork J ω q : ℝ) ∂Measure.infinitePi (fun _ : ℕ => ν) =
      q * ∫ t, (tailWork J t : ℝ) ∂ν := @stream_expected_work
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (J q b : ℕ) (hb : 0 < b),
    (Measure.infinitePi (fun _ : ℕ => ν)).real {ω | b < probeWork J ω q} ≤
      q * (∫ t, (tailWork J t : ℝ) ∂ν) / b := @stream_work_exceeds_le
example : ∀ {J b M : ℕ} {ω : ℕ → ℕ → Bool} {F u : ℝ} (hF1 : F ≤ 1) (hFu : F ≤ 2 * u) (h : probeUpper (probeCompleted J b M ω) < F),
    0 < u ∧ ∀ i < ⌊4 / u⌋₊, ¬ tailUnresolved J (ω i) := @resolved_prefix_of_upper_lt
example :
    exp (-3) ≤ 1 / 8 := @exp_neg_three_le
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (J : ℕ) {F : ℝ} (hF1 : F ≤ 1) (hFu : F ≤ 2 * ν.real {t | tailUnresolved J t}),
    (Measure.infinitePi (fun _ : ℕ => ν)).real
      {ω | ∃ b M, probeUpper (probeCompleted J b M ω) < F} ≤ 1 / 8 := @stream_probe_invalid_le
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (J : ℕ) {F : ℝ} (hF1 : F ≤ 1) (hFu : F ≤ 2 * ν.real {t | tailUnresolved J t}),
    7 / 8 ≤ (Measure.infinitePi (fun _ : ℕ => ν)).real
      {ω | ∀ b M, F ≤ probeUpper (probeCompleted J b M ω)} := @stream_probe_valid
example : ∀ (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν] (J b M : ℕ) (hb : 0 < b) (hM : 0 < M) {W : ℝ} (hW : ∫ t, (tailWork J t : ℝ) ∂ν ≤ W),
    3 / 4 ≤ (Measure.infinitePi (fun _ : ℕ => ν)).real
      {ω | probeUpper (probeCompleted J b M ω) ≤
      min 1 (128 * max (max (ν.real {t | tailUnresolved J t}) (W / b)) (1 / M))} := @stream_probe_performance
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw),
    (originalSimulationLaw μ A q).map Prod.snd =
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q) := @originalSimulationLaw_coins
example : ∀ (J : ℕ) (d : Gap),
    1 ≤ tailWorkEnvelope J d := @one_le_tailWorkEnvelope
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (J : ℕ),
    1 ≤ ∫ d : Gap, tailWorkEnvelope J d ∂μ := @one_le_tailWorkEnvelope_integral
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J : ℕ),
    7 / 8 ≤ (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | ∀ b M, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
      probeUpper (probeCompleted J b M ω)} := @original_probe_valid
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J b M : ℕ) (hb : 0 < b) (hM : 0 < M),
    3 / 4 ≤ (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | probeUpper (probeCompleted J b M ω) ≤
      min 1 (128 * max (max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M))} := @original_probe_performance
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J b M : ℕ) (hb : 0 < b) (hbM : b ≤ M),
    3 / 4 ≤ (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | probeUpper (probeCompleted J b M ω) ≤
      min 1 (128 * max (tailUnresolvedMass μ J)
      ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b))} := @original_probe_performance_uncapped
"""
    if source.count("example ") != len(NAMES):
        raise ValueError("Each tail-probe declaration needs exactly one restated statement")
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
