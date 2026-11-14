"""Audit the sign-neutral single-coin tail test of the arbitrary-law tail certificate.

Every definition and theorem of the three tail-test modules is restated in
full, so a changed definition, hypothesis or constant is an elaboration error,
and the transitive axioms of every declaration are reported. A declaration in
those modules that is not registered here is an error. Prints the kernel
report; writes nothing.
"""

import subprocess
from verify_blind_upper_components import (FORBIDDEN, LEAN, bind_restatements,
                                           registered_names, strip_comments,
                                           validate_reports)

MODULE = "ThresholdHC.ArbitraryLawAdaptation.TailTestLaw"
SOURCES = [LEAN / "ThresholdHC/ArbitraryLawAdaptation" / (name + ".lean")
           for name in ("TailTest", "TailTestProbability", "TailTestLaw")]
NAMES = [
    "tailHeads", "tailScale", "tailThreshold", "tailResolvedAt", "tailUnresolved", "tailStop",
    "tailWork", "tapeFlip", "tailHeads_le", "tailHeads_congr", "tailHeads_flip",
    "prefixMean_eq_heads", "tailScale_le_threshold_sq", "tailThreshold_lt",
    "tailThreshold_le_iff", "tailThreshold_terminal", "tailResolvedAt_iff", "tailStop_le",
    "tailStop_mem", "not_resolved_of_lt_stop", "tailWork_pos", "tailWork_le",
    "tailUnresolved_iff", "tailResolvedAt_congr", "tailStop_congr", "tailWork_congr",
    "tailUnresolved_congr", "tailResolvedAt_flip", "tailStop_flip", "tailWork_flip",
    "tailUnresolved_flip", "measurable_of_tape_prefix", "measurable_tailHeads",
    "measurable_tailStop", "measurable_tailWork", "measurable_tapeFlip",
    "measurableSet_tailResolvedAt", "measurableSet_tailUnresolved", "gapParameter_true_coe",
    "tailLog", "tailWorkEnvelope", "exp_neg_one_le", "exp_neg_nat_le", "tail_geometric_sum",
    "tailThreshold_ge", "tailScale_cast", "tail_not_resolved_le_exp", "tail_resolved_le_exp",
    "tail_resolved_small_gap", "tail_unresolved_ge_half", "tail_unresolved_le_exp",
    "tailThreshold_le_of_scale", "tail_work_term", "four_pow_layer", "tailWork_sum",
    "integrable_tailWork", "measurableSet_stop_gt", "tail_expected_work_eq",
    "tail_expected_work_le", "tapeMeasure_flip", "gapParameter_false_eq",
    "tapeMeasure_flip_invariant", "tape_integral_flip", "tailStop_law_sign_neutral",
    "tailUnresolved_flip_preimage", "tailUnresolved_sign_neutral", "parameterTape_integral",
    "measurable_tape_integral", "tape_integral_abs_le", "original_tape_integral_sign_neutral",
    "tailUnresolvedProb", "tailUnresolvedMass", "tailUnresolvedProb_eq_integral",
    "measurable_tailUnresolvedProb", "tailUnresolvedProb_nonneg", "tailUnresolvedProb_le_one",
    "integrable_tailUnresolvedProb", "original_tail_unresolved", "tail_unresolved_mass_lower",
    "tailUnresolvedProb_le_exp", "four_pow_half_pow", "tailUnresolvedProb_le_envelope",
    "tail_unresolved_mass_upper", "tailUnresolvedProb_le_lightCDF",
    "tail_unresolved_mass_le_multiplier", "tailLog_nonneg", "tailWorkEnvelope_le",
    "tailWorkEnvelope_nonneg", "measurable_tailWorkEnvelope", "tail_expected_work_le_sign",
    "original_tail_expected_work",
]


def declared_names():
    """Every declaration of the three modules, after rejecting proof escapes."""
    found = []
    for path in SOURCES:
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + path.name)
        found += registered_names(source)
    return found


def audit_input():
    if sorted(declared_names()) != sorted(NAMES):
        raise ValueError("Unregistered or missing tail-test declaration")
    source = """
import ThresholdHC.ArbitraryLawAdaptation.TailTestLaw
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Real ProbabilityTheory
open scoped ENNReal
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.Tier2 ThresholdHC.Tier6
open ThresholdHC.Uniform713 ThresholdHC.EntropyTailUpper ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation

example : ∀ (n : ℕ) (ω : ℕ → Bool), tailHeads n ω = ∑ i ∈ Finset.range n, (ω i).toNat :=
  fun _ _ => rfl
example : ∀ J k : ℕ, tailScale J k = 2 * 4 ^ k * (J - k + 2) := fun _ _ => rfl
example : ∀ J k : ℕ, tailThreshold J k = ⌈Real.sqrt (tailScale J k)⌉₊ := fun _ _ => rfl
example : ∀ (J k : ℕ) (ω : ℕ → Bool), tailResolvedAt J k ω ↔
    2 * (tailThreshold J k : ℤ) < |2 * (tailHeads (4 ^ k) ω : ℤ) - ((4 ^ k : ℕ) : ℤ)| :=
  fun _ _ _ => Iff.rfl
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    tailUnresolved J ω ↔ ∀ k, k ≤ J → ¬ tailResolvedAt J k ω := fun _ _ => Iff.rfl
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    tailStop J ω = sInf {k | J ≤ k ∨ tailResolvedAt J k ω} := fun _ _ => rfl
example : ∀ (J : ℕ) (ω : ℕ → Bool), tailWork J ω = 4 ^ tailStop J ω := fun _ _ => rfl
example : ∀ (ω : ℕ → Bool) (i : ℕ), tapeFlip ω i = !ω i := fun _ _ => rfl
example : ∀ (J : ℕ) (d : ℝ), tailLog J d = max 0 (Real.logb 2 (d * 2 ^ J)) := fun _ _ => rfl
example : ∀ (J : ℕ) (d : ℝ),
    tailWorkEnvelope J d = min (4 ^ J) (1024 / d ^ 2 * (1 + tailLog J d)) := fun _ _ => rfl
example : ∀ (J : ℕ) (d : Gap), tailUnresolvedProb J d =
    (tapeMeasure (gapParameter true d)).real {ω | tailUnresolved J ω} := fun _ _ => rfl
example : ∀ (μ : Measure Gap) (J : ℕ),
    tailUnresolvedMass μ J = ∫ d, tailUnresolvedProb J d ∂μ := fun _ _ => rfl

example : ∀ (n : ℕ) (ω : ℕ → Bool),
    tailHeads n ω ≤ n := @tailHeads_le
example : ∀ {n : ℕ} {ω ω' : ℕ → Bool} (h : ∀ i < n, ω i = ω' i),
    tailHeads n ω = tailHeads n ω' := @tailHeads_congr
example : ∀ (n : ℕ) (ω : ℕ → Bool),
    tailHeads n (tapeFlip ω) = n - tailHeads n ω := @tailHeads_flip
example : ∀ (n : ℕ) (ω : ℕ → Bool),
    prefixMean observations n ω = (tailHeads n ω : ℝ) / n := @prefixMean_eq_heads
example : ∀ (J k : ℕ),
    (tailScale J k : ℝ) ≤ (tailThreshold J k : ℝ) ^ 2 := @tailScale_le_threshold_sq
example : ∀ (J k : ℕ),
    (tailThreshold J k : ℝ) < Real.sqrt (tailScale J k) + 1 := @tailThreshold_lt
example : ∀ (J k a : ℕ),
    tailThreshold J k ≤ a ↔ tailScale J k ≤ a ^ 2 := @tailThreshold_le_iff
example : ∀ (J : ℕ),
    tailThreshold J J = 2 ^ (J + 1) := @tailThreshold_terminal
example : ∀ (J k : ℕ) (ω : ℕ → Bool),
    tailResolvedAt J k ω ↔
      (tailThreshold J k : ℝ) / 4 ^ k < |prefixMean observations (4 ^ k) ω - 1 / 2| := @tailResolvedAt_iff
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    tailStop J ω ≤ J := @tailStop_le
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    J ≤ tailStop J ω ∨ tailResolvedAt J (tailStop J ω) ω := @tailStop_mem
example : ∀ {J k : ℕ} {ω : ℕ → Bool} (h : k < tailStop J ω),
    ¬ tailResolvedAt J k ω := @not_resolved_of_lt_stop
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    1 ≤ tailWork J ω := @tailWork_pos
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    tailWork J ω ≤ 4 ^ J := @tailWork_le
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    tailUnresolved J ω ↔ ¬ tailResolvedAt J (tailStop J ω) ω := @tailUnresolved_iff
example : ∀ {J k : ℕ} {ω ω' : ℕ → Bool} (h : ∀ i < 4 ^ k, ω i = ω' i),
    tailResolvedAt J k ω ↔ tailResolvedAt J k ω' := @tailResolvedAt_congr
example : ∀ {J : ℕ} {ω ω' : ℕ → Bool} (h : ∀ i < tailWork J ω, ω i = ω' i),
    tailStop J ω' = tailStop J ω := @tailStop_congr
example : ∀ {J : ℕ} {ω ω' : ℕ → Bool} (h : ∀ i < tailWork J ω, ω i = ω' i),
    tailWork J ω' = tailWork J ω := @tailWork_congr
example : ∀ {J : ℕ} {ω ω' : ℕ → Bool} (h : ∀ i < tailWork J ω, ω i = ω' i),
    tailUnresolved J ω' ↔ tailUnresolved J ω := @tailUnresolved_congr
example : ∀ (J k : ℕ) (ω : ℕ → Bool),
    tailResolvedAt J k (tapeFlip ω) ↔ tailResolvedAt J k ω := @tailResolvedAt_flip
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    tailStop J (tapeFlip ω) = tailStop J ω := @tailStop_flip
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    tailWork J (tapeFlip ω) = tailWork J ω := @tailWork_flip
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    tailUnresolved J (tapeFlip ω) ↔ tailUnresolved J ω := @tailUnresolved_flip
example : ∀ {α : Type*} [MeasurableSpace α] (M : ℕ) (f : (ℕ → Bool) → α) (h : ∀ ω ω', (∀ i < M, ω i = ω' i) → f ω = f ω'),
    Measurable f := @measurable_of_tape_prefix
example : ∀ (n : ℕ),
    Measurable (tailHeads n) := @measurable_tailHeads
example : ∀ (J : ℕ),
    Measurable (tailStop J) := @measurable_tailStop
example : ∀ (J : ℕ),
    Measurable (tailWork J) := @measurable_tailWork
example : Measurable tapeFlip := measurable_tapeFlip
example : ∀ (J k : ℕ),
    MeasurableSet {ω | tailResolvedAt J k ω} := @measurableSet_tailResolvedAt
example : ∀ (J : ℕ),
    MeasurableSet {ω | tailUnresolved J ω} := @measurableSet_tailUnresolved
example : ∀ (d : Gap),
    ((gapParameter true d : unitInterval) : ℝ) = 1 / 2 + (d : ℝ) := @gapParameter_true_coe
example : exp (-1) ≤ 10 / 27 := exp_neg_one_le
example : ∀ (m : ℕ),
    exp (-(m : ℝ)) ≤ (10 / 27) ^ m := @exp_neg_nat_le
example : ∀ (J : ℕ),
    ∑ k ∈ Finset.range (J + 1), ((10 : ℝ) / 27) ^ (J - k) ≤ 27 / 17 := @tail_geometric_sum
example : ∀ (J k : ℕ),
    2 * (2 : ℝ) ^ k ≤ (tailThreshold J k : ℝ) := @tailThreshold_ge
example : ∀ (J k : ℕ),
    (tailScale J k : ℝ) = 2 * 4 ^ k * ((J - k + 2 : ℕ) : ℝ) := @tailScale_cast
example : ∀ (J k : ℕ) (d : Gap) (hr : 2 * (tailThreshold J k : ℝ) ≤ 4 ^ k * (d : ℝ)),
    (tapeMeasure (gapParameter true d)).real {ω | ¬ tailResolvedAt J k ω} ≤
      exp (-(4 ^ k * (d : ℝ) ^ 2 / 2)) := @tail_not_resolved_le_exp
example : ∀ (J k : ℕ) (d : Gap) (hd : 2 * (4 ^ k * (d : ℝ)) ≤ (tailThreshold J k : ℝ)),
    (tapeMeasure (gapParameter true d)).real {ω | tailResolvedAt J k ω} ≤
      2 * exp (-((tailThreshold J k : ℝ) ^ 2 / (2 * 4 ^ k))) := @tail_resolved_le_exp
example : ∀ (J k : ℕ) (hk : k ≤ J) (d : Gap) (hd : (d : ℝ) ≤ (1 / 2) ^ J),
    (tapeMeasure (gapParameter true d)).real {ω | tailResolvedAt J k ω} ≤
      2 * (10 / 27 : ℝ) ^ (J - k + 2) := @tail_resolved_small_gap
example : ∀ (J : ℕ) (d : Gap) (hd : (d : ℝ) ≤ (1 / 2) ^ J),
    1 / 2 ≤ (tapeMeasure (gapParameter true d)).real {ω | tailUnresolved J ω} := @tail_unresolved_ge_half
example : ∀ (J : ℕ) (d : Gap) (hd : 4 * (1 / 2 : ℝ) ^ J ≤ (d : ℝ)),
    (tapeMeasure (gapParameter true d)).real {ω | tailUnresolved J ω} ≤
      exp (-(4 ^ J * (d : ℝ) ^ 2 / 2)) := @tail_unresolved_le_exp
example : ∀ (J k : ℕ) {d : ℝ} (hd : 0 ≤ d) (hC : 36 * ((J - k + 2 : ℕ) : ℝ) ≤ 4 ^ k * d ^ 2),
    2 * (tailThreshold J k : ℝ) ≤ 4 ^ k * d := @tailThreshold_le_of_scale
example : ∀ (k0 j : ℕ) {d : ℝ} (hk0 : 72 ≤ 4 ^ k0 * d ^ 2),
    3 * (4 : ℝ) ^ (k0 + j) * exp (-(4 ^ (k0 + j) * d ^ 2 / 2)) ≤ 4 ^ k0 * (1 / 2) ^ j / 2 := @tail_work_term
example : ∀ (J s : ℕ) (hs : s ≤ J),
    (4 : ℝ) ^ s = 1 + ∑ k ∈ Finset.range J, 3 * 4 ^ k * (if k < s then (1 : ℝ) else 0) := @four_pow_layer
example : ∀ (J : ℕ) (ω : ℕ → Bool),
    (tailWork J ω : ℝ) =
      1 + ∑ k ∈ Finset.range J, 3 * 4 ^ k * (if k < tailStop J ω then (1 : ℝ) else 0) := @tailWork_sum
example : ∀ (J : ℕ) (P : Measure (ℕ → Bool)) [IsFiniteMeasure P],
    Integrable (fun ω => (tailWork J ω : ℝ)) P := @integrable_tailWork
example : ∀ (J k : ℕ),
    MeasurableSet {ω | k < tailStop J ω} := @measurableSet_stop_gt
example : ∀ (J : ℕ) (P : Measure (ℕ → Bool)) [IsProbabilityMeasure P],
    ∫ ω, (tailWork J ω : ℝ) ∂P =
      1 + ∑ k ∈ Finset.range J, 3 * 4 ^ k * P.real {ω | k < tailStop J ω} := @tail_expected_work_eq
example : ∀ (J : ℕ) (d : Gap),
    ∫ ω, (tailWork J ω : ℝ) ∂tapeMeasure (gapParameter true d) ≤ tailWorkEnvelope J d := @tail_expected_work_le
example : ∀ (p : unitInterval),
    (tapeMeasure p).map tapeFlip = tapeMeasure (unitInterval.symm p) := @tapeMeasure_flip
example : ∀ (d : Gap),
    gapParameter false d = unitInterval.symm (gapParameter true d) := @gapParameter_false_eq
example : ∀ (d : Gap) {S : Set (ℕ → Bool)} (hS : MeasurableSet S) (hflip : tapeFlip ⁻¹' S = S),
    tapeMeasure (gapParameter false d) S = tapeMeasure (gapParameter true d) S := @tapeMeasure_flip_invariant
example : ∀ (p : unitInterval) (G : (ℕ → Bool) → ℝ) (hG : Measurable G) (hflip : ∀ t, G (tapeFlip t) = G t),
    ∫ t, G t ∂tapeMeasure (unitInterval.symm p) = ∫ t, G t ∂tapeMeasure p := @tape_integral_flip
example : ∀ (J : ℕ) (d : Gap),
    (tapeMeasure (gapParameter false d)).map (tailStop J) =
      (tapeMeasure (gapParameter true d)).map (tailStop J) := @tailStop_law_sign_neutral
example : ∀ (J : ℕ),
    tapeFlip ⁻¹' {ω | tailUnresolved J ω} = {ω | tailUnresolved J ω} := @tailUnresolved_flip_preimage
example : ∀ (J : ℕ) (d : Gap),
    tapeMeasure (gapParameter false d) {ω | tailUnresolved J ω} =
      tapeMeasure (gapParameter true d) {ω | tailUnresolved J ω} := @tailUnresolved_sign_neutral
example : ∀ (κ : Measure unitInterval) [IsProbabilityMeasure κ] (F : (ℕ → Bool) → ℝ) (hF : Measurable F) {M : ℝ} (hb : ∀ t, |F t| ≤ M),
    (∫ t, F t ∂parameterTapeLaw κ) = ∫ p, (∫ t, F t ∂tapeMeasure p) ∂κ := @parameterTape_integral
example : ∀ (F : (ℕ → Bool) → ℝ) (hF : Measurable F),
    Measurable (fun p : unitInterval => ∫ t, F t ∂tapeMeasure p) := @measurable_tape_integral
example : ∀ (p : unitInterval) (G : (ℕ → Bool) → ℝ) {M : ℝ} (hb : ∀ t, |G t| ≤ M),
    |∫ t, G t ∂tapeMeasure p| ≤ M := @tape_integral_abs_le
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (G : (ℕ → Bool) → ℝ) (hG : Measurable G) {M : ℝ} (hb : ∀ t, |G t| ≤ M) (hflip : ∀ t, G (tapeFlip t) = G t),
    ∫ t, G t ∂originalPopulationTapeLaw μ q =
      ∫ d, (∫ t, G t ∂tapeMeasure (gapParameter true d)) ∂μ := @original_tape_integral_sign_neutral
example : ∀ (J : ℕ) (d : Gap),
    tailUnresolvedProb J d = ∫ t, Set.indicator {ω | tailUnresolved J ω} (fun _ => (1 : ℝ)) t
      ∂tapeMeasure (gapParameter true d) := @tailUnresolvedProb_eq_integral
example : ∀ (J : ℕ),
    Measurable (tailUnresolvedProb J) := @measurable_tailUnresolvedProb
example : ∀ (J : ℕ) (d : Gap),
    0 ≤ tailUnresolvedProb J d := @tailUnresolvedProb_nonneg
example : ∀ (J : ℕ) (d : Gap),
    tailUnresolvedProb J d ≤ 1 := @tailUnresolvedProb_le_one
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (J : ℕ),
    Integrable (tailUnresolvedProb J) μ := @integrable_tailUnresolvedProb
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J : ℕ),
    (originalPopulationTapeLaw μ q).real {ω | tailUnresolved J ω} = tailUnresolvedMass μ J := @original_tail_unresolved
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (J : ℕ),
    μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} / 2 ≤ tailUnresolvedMass μ J := @tail_unresolved_mass_lower
example : ∀ (J : ℕ) (d : Gap) (hd : 4 * (1 / 2 : ℝ) ^ J ≤ (d : ℝ)),
    tailUnresolvedProb J d ≤ exp (-(4 ^ J * (d : ℝ) ^ 2 / 2)) := @tailUnresolvedProb_le_exp
example : ∀ (J : ℕ),
    (4 : ℝ) ^ J * ((1 / 2 : ℝ) ^ J) ^ 2 = 1 := @four_pow_half_pow
example : ∀ (J : ℕ) (d : Gap),
    tailUnresolvedProb J d ≤ min 1 (16 * ((1 / 2) ^ J / (d : ℝ)) ^ 2) := @tailUnresolvedProb_le_envelope
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (J : ℕ),
    tailUnresolvedMass μ J ≤ ∫ d : Gap, min 1 (16 * ((1 / 2) ^ J / (d : ℝ)) ^ 2) ∂μ := @tail_unresolved_mass_upper
example : ∀ (J : ℕ) (d : Gap),
    tailUnresolvedProb J d ≤ lightCDF ((1 / 2) ^ J / (d : ℝ)) := @tailUnresolvedProb_le_lightCDF
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (J : ℕ),
    ENNReal.ofReal (tailUnresolvedMass μ J) ≤
      (μ.prod lightMultiplier) {z : Gap × Gap | (z.1 : ℝ) * (z.2 : ℝ) ≤ (1 / 2) ^ J} := @tail_unresolved_mass_le_multiplier
example : ∀ (J : ℕ) (d : ℝ),
    0 ≤ tailLog J d := @tailLog_nonneg
example : ∀ (J : ℕ) (d : ℝ),
    tailWorkEnvelope J d ≤ 4 ^ J := @tailWorkEnvelope_le
example : ∀ (J : ℕ) (d : ℝ),
    0 ≤ tailWorkEnvelope J d := @tailWorkEnvelope_nonneg
example : ∀ (J : ℕ),
    Measurable (tailWorkEnvelope J) := @measurable_tailWorkEnvelope
example : ∀ (J : ℕ) (s : Bool) (d : Gap),
    ∫ ω, (tailWork J ω : ℝ) ∂tapeMeasure (gapParameter s d) ≤ tailWorkEnvelope J d := @tail_expected_work_le_sign
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J : ℕ),
    ∫ t, (tailWork J t : ℝ) ∂originalPopulationTapeLaw μ q ≤
      ∫ d : Gap, tailWorkEnvelope J d ∂μ := @original_tail_expected_work
"""
    bind_restatements(source, NAMES)
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
