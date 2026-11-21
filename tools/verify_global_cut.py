"""Audit Corollary 6 of the certified-selection note: the global-cut bound.

The best global upper-gap cut V, the selection objective minimized over the
cuts that keep the gaps above a threshold in the entropy core, satisfies
K <= V <= Q <= (8/5) K for every probability law of gaps, 0 < rho <= 1/4 and
B > 0, where K is the selection functional and Q the closed quantile value.
On n atoms in increasing order V is the capped minimum over the n+1 top-k
cuts, the selections scanned by the toolkit's threshold_certificate. On the
note's two-atom law V is strictly above K, so the cut is not exact.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the three targets and three components with their types written out;
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

GROUP = "GlobalCut"
NAMES = ("Specification", "Cut", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "55f07fcdf6eef2e9313a26cd9266c9cde903f3650b7f94af917cd4f22b3efad0"
TARGETS = {
    "GlobalCut.global_cut": "GlobalCut.GlobalCutStatement",
    "GlobalCut.finite_cut": "GlobalCut.FiniteCutStatement",
    "GlobalCut.not_exact": "GlobalCut.NotExactStatement",
}
COMPONENTS = (
    "GlobalCut.selection_le_globalCutValue",
    "GlobalCut.globalCutValue_le_closedQuantileValue",
    "GlobalCut.rpow_half_mix",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    selection μ ρ B ≤ globalCutValue μ ρ B ∧
    globalCutValue μ ρ B ≤ EntropyTailQuantile.closedQuantileValue μ ρ B ∧
    EntropyTailQuantile.closedQuantileValue μ ρ B ≤ ENNReal.ofReal (8/5) * selection μ ρ B :=
  GlobalCut.global_cut

example :
  ∀ {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℝ≥0∞), StrictMono d → ∀ ρ B : ℝ,
    globalCutValue (∑ i, w i • Measure.dirac (d i)) ρ B =
      min (ENNReal.ofReal ρ) (⨅ k : Fin (n+1),
        selectionObjective (∑ i, w i • Measure.dirac (d i)) ρ B
          (∑ i : Fin n, (if n ≤ i.val + k.val then w i else 0) • Measure.dirac (d i))) :=
  GlobalCut.finite_cut

example :
  ∃ a b : Gap, (a : ℝ) = 1/4 ∧ (b : ℝ) = 1/2 ∧
    let μ := ENNReal.ofReal (9999/10000) • Measure.dirac a +
      ENNReal.ofReal (1/10000) • Measure.dirac b
    IsProbabilityMeasure μ ∧ selection μ (1/4) (10^8) < globalCutValue μ (1/4) (10^8) :=
  GlobalCut.not_exact

example : ∀ (μ : Measure Gap) (ρ B : ℝ), selection μ ρ B ≤ globalCutValue μ ρ B :=
  @GlobalCut.selection_le_globalCutValue

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ}, 0 < ρ → ρ ≤ 1 → ∀ (B : ℝ),
    globalCutValue μ ρ B ≤ EntropyTailQuantile.closedQuantileValue μ ρ B :=
  @GlobalCut.globalCutValue_le_closedQuantileValue

example : ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 → ∀ (x y : ℝ≥0∞),
    ENNReal.ofReal r * x ^ (1/2 : ℝ) + ENNReal.ofReal (1-r) * y ^ (1/2 : ℝ) ≤
      (ENNReal.ofReal r * x + ENNReal.ofReal (1-r) * y) ^ (1/2 : ℝ) :=
  @GlobalCut.rpow_half_mix
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
        raise ValueError("Duplicate global-cut declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing global-cut target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed global-cut specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.GlobalCut",
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
    print(f"All {len(TARGETS)} global-cut targets are certified")


if __name__ == "__main__":
    main()
