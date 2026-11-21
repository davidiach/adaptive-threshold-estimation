"""Audit the Hoeffding replication count of the finite-cell observable-state bound.

The proof of Proposition prop:outer (paper/v6/core.tex) replicates each
rounded magnitude in M cells with unknown fixed signs, bounds the sign
target's deviation by weighted Hoeffding, 2 exp(-M Delta^2/32), and takes an
integer M >= 32 Delta^-2 log(2/delta). The checked construction of
ObservedState.finite_observed_state_lower used the second-moment count
M^-1 <= delta Delta^2/16 instead, and Appendix app:finite-observed records the
Hoeffding count as a paper bound. The group checks weighted Hoeffding for the
sign target, the replication tail, the finite-cell testing lower bound under
the Hoeffding weight condition, its form for every finite measurable cell
design, and the proposition with the least admissible count.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the five targets and three components with their types written out;
4. reports the transitive axioms of every public declaration in the directory.

With --replay the registered modules also go through the toolchain's
independent kernel checker. The statements were written after the proofs;
they are pinned from this audit onward.
"""

from __future__ import annotations

import argparse
import re
import subprocess

from verify_blind_upper_components import FORBIDDEN, LEAN, sha, strip_comments, validate_reports
from verify_sharp_rms import public_names

GROUP = "ObservedHoeffding"
NAMES = ("Specification", "Hoeffding", "Lower", "Construction", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "16f438bd16dc72f026bc5f1d9980a2b62647dd8cd86759ee154694786692caa2"
TARGETS = {
    "ObservedHoeffding.weighted_hoeffding_target": "ObservedHoeffding.WeightedHoeffdingStatement",
    "ObservedHoeffding.replication_tail_target": "ObservedHoeffding.ReplicationTailStatement",
    "ObservedHoeffding.hoeffding_confidence_lower_target": "ObservedHoeffding.HoeffdingConfidenceLowerStatement",
    "ObservedHoeffding.hoeffding_design_lower_target": "ObservedHoeffding.HoeffdingDesignLowerStatement",
    "ObservedHoeffding.hoeffding_finite_observed": "ObservedHoeffding.HoeffdingFiniteObservedStatement",
}
COMPONENTS = (
    "ObservedHoeffding.replication_exp_le",
    "ObservedHoeffding.cellDelta_pos",
    "ObservedHoeffding.injective_range_labels",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ {I : Type} [Fintype I] (q : I → unitInterval) (w : I → ℝ) {v r : ℝ},
    (∀ i, 0 ≤ w i) → 0 < v → (∑ i, (w i) ^ 2) ≤ v → 0 ≤ r →
    signLaw q {s | r < |target w s - ∑ i, w i * (q i : ℝ)|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * r ^ 2 / v)) :=
  ObservedHoeffding.weighted_hoeffding_target

example :
  ∀ {I : Type} [Fintype I] (q : I → unitInterval) (w : I → ℝ) (M : ℕ) {Δ δ : ℝ},
    (∀ i, 0 ≤ w i) → 0 < M → (∑ i, (w i) ^ 2) ≤ 1 / (M : ℝ) → 0 < Δ → 0 < δ →
    32 * Real.log (2 / δ) / Δ ^ 2 ≤ (M : ℝ) →
    signLaw q {s | Δ / 8 < |target w s - ∑ i, w i * (q i : ℝ)|} ≤
        ENNReal.ofReal (2 * Real.exp (-(M : ℝ) * Δ ^ 2 / 32)) ∧
      2 * Real.exp (-(M : ℝ) * Δ ^ 2 / 32) ≤ δ :=
  ObservedHoeffding.replication_tail_target

example :
  ∀ {m : ℕ} {R : Type} [MeasurableSpace R] (A : Estimator m R) (d : Fin m → Gap)
    (w η : Fin m → ℝ) (qp qm : Fin m → unitInterval),
    (∀ i, (qp i : ℝ) = 1 / 2 + η i) → (∀ i, (qm i : ℝ) = 1 / 2 - η i) →
    ∀ {B h Δ δ : ℝ}, 0 ≤ B → 0 < h → 0 < Δ → 0 < δ → δ ≤ 1 / 8 →
    (∀ i, 0 ≤ η i ∧ η i ≤ 1 / 8) → (∀ i, (d i : ℝ) * η i ≤ h / 8) →
    (∑ i, w i * (qp i : ℝ)) - (∑ i, w i * (qm i : ℝ)) = Δ →
    (∀ i, 0 ≤ w i) → 32 * Real.log (2 / δ) * (∑ i, (w i) ^ 2) ≤ Δ ^ 2 →
    (∀ s, ThresholdHC.ObservedState.expectedWork A d s ≤ ENNReal.ofReal B) →
    UniformConfidence A d w (Δ / 4) δ →
    (225 / (128 * h ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B :=
  ObservedHoeffding.hoeffding_confidence_lower_target

example :
  ∀ (h : Gap) {N : ℕ} (cap : Fin N → Gap) (cell : unitInterval → Fin N) (hc : Measurable cell)
    {δ : ℝ}, 0 < δ → δ ≤ 1 / 8 →
    32 * Real.log (2 / δ) * (∑ i, (cellWeight cell i) ^ 2) ≤ (cellDelta cap cell h) ^ 2 →
    ∀ (R : Type) [MeasurableSpace R] (A : StateEstimator R) (B : ℝ), 0 ≤ B →
      (∀ s, (∫⁻ z, totalProcessWork z.2 ∂stateLaw A cap cell hc s) ≤ ENNReal.ofReal B) →
      (∀ s, stateLaw A cap cell hc s
        {z | cellDelta cap cell h / 4 < |A.output z - stateTarget cell s|} ≤ ENNReal.ofReal δ) →
      (225 / (128 * (h : ℝ) ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B :=
  ObservedHoeffding.hoeffding_design_lower_target

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (h : Gap) {δ : ℝ}, 0 < δ → δ ≤ 1 / 8 →
    ∃ (N M : ℕ) (c : Fin N → Gap) (v : Fin N → ℝ) (cap : Fin (N * M) → Gap)
      (gap : unitInterval → Gap) (cell : unitInterval → Fin (N * M)) (hc : Measurable cell),
      Measurable gap ∧ volume.map gap = μ ∧ (∀ u, gap u ≤ cap (cell u)) ∧
      Function.Injective c ∧ (∀ j, 0 ≤ v j) ∧ (∑ j, v j) = 1 ∧
      (∀ j k, cap (finProdFinEquiv (j, k)) = c j) ∧
      (∀ j k, cellWeight cell (finProdFinEquiv (j, k)) = v j / (M : ℝ)) ∧
      0 < M ∧ M = ⌈32 * Real.log (2 / δ) / (cellDelta cap cell h) ^ 2⌉₊ ∧
      (∑ i, (cellWeight cell i) ^ 2) ≤ 1 / (M : ℝ) ∧
      2 * Real.exp (-(M : ℝ) * (cellDelta cap cell h) ^ 2 / 32) ≤ δ ∧
      0 < cellDelta cap cell h ∧
      modulus μ h / 8 ≤ cellDelta cap cell h ∧
      (∀ x : ℝ, volume {u : unitInterval | (cap (cell u) : ℝ) ≤ x} ≤ μ {d : Gap | (d : ℝ) ≤ x}) ∧
      (∀ (R : Type) [MeasurableSpace R] (A : StateEstimator R) (B : ℝ), 0 ≤ B →
        (∀ s, (∫⁻ z, totalProcessWork z.2 ∂stateLaw A cap cell hc s) ≤ ENNReal.ofReal B) →
        (∀ s, stateLaw A cap cell hc s
          {z | cellDelta cap cell h / 4 < |A.output z - stateTarget cell s|} ≤ ENNReal.ofReal δ) →
        (225 / (128 * (h : ℝ) ^ 2)) * klB (1 - 2 * δ) (2 * δ) ≤ B) :=
  ObservedHoeffding.hoeffding_finite_observed

example : ∀ {M Δ δ : ℝ}, 0 < Δ → 0 < δ → 32 * Real.log (2 / δ) / Δ ^ 2 ≤ M →
    2 * Real.exp (-M * Δ ^ 2 / 32) ≤ δ :=
  @ObservedHoeffding.replication_exp_le

example : ∀ (h : Gap) {N : ℕ} (cap : Fin N → Gap) (cell : unitInterval → Fin N),
    Measurable cell → 0 < cellDelta cap cell h :=
  @ObservedHoeffding.cellDelta_pos

example : ∀ (T : Gap → Gap), Measurable T → (Set.range T).Finite →
    ∃ N : ℕ, 0 < N ∧ ∃ (cap : Fin N → Gap) (label : Gap → Fin N),
      Function.Injective cap ∧ Measurable label ∧ ∀ d, cap (label d) = T d :=
  @ObservedHoeffding.injective_range_labels
"""


def modules() -> list[str]:
    return [f"{GROUP}.{name}" for name in NAMES]


def declared_roots() -> set[str]:
    found = {p.stem for p in SOURCE.glob("*.lean")}
    if found != set(NAMES) or len(NAMES) != len(set(NAMES)):
        raise ValueError(f"Unregistered or missing {GROUP} module")
    roots: list[str] = []
    for name in NAMES:
        source = strip_comments((SOURCE / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in {GROUP}/{name}.lean")
        names_here = public_names(source, f"{GROUP}/{name}.lean")
        if any(not root.startswith(f"ThresholdHC.{GROUP}.") for root in names_here):
            raise ValueError(f"{GROUP}/{name}.lean must declare in ThresholdHC.{GROUP}")
        roots.extend(names_here)
    if len(roots) != len(set(roots)):
        raise ValueError("Duplicate observed-hoeffding declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing observed-hoeffding target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed observed-hoeffding specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservedState ThresholdHC.ObservedHoeffding",
        *[f"example : {statement} := {theorem}" for theorem, statement in sorted(TARGETS.items())],
        EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    if ("\n" + EXACT).count("\nexample") != EXACT_COUNT:
        raise ValueError("Each target and component needs exactly one restated statement")
    for name in list(TARGETS) + list(COMPONENTS):
        if len(re.findall(rf":=\s*@?{re.escape(name)}\n", EXACT)) != 1:
            raise ValueError("Each target and component needs exactly one restated statement")
    return source, roots


def replay_modules() -> list[str]:
    return ["ThresholdHC." + module for module in modules()]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--replay", action="store_true",
                        help="also replay the registered modules through leanchecker")
    parser.add_argument("--jobs", type=int, default=3, help="parallel kernel replays")
    args = parser.parse_args()
    source, roots = audit_input()
    subprocess.run(["lake", "build", *replay_modules()], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {EXACT_COUNT} exact statements and {len(roots)} transitive axiom reports")
    if args.replay:
        from verify_project_axioms import replay
        replay(replay_modules(), "lake", args.jobs)
        print(f"Replayed {len(modules())} modules through the independent kernel checker")
    print(f"All {len(TARGETS)} observed-hoeffding targets are certified")


if __name__ == "__main__":
    main()
