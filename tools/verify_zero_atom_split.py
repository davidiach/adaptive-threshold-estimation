"""Audit the zero-atom split of the selection functional.

For alpha = z delta_0 + (1 - z) eta, with eta a probability law of positive
gaps, 0 <= z < 1, rho > 0 and B > 0:

    K_alpha(B) = min{rho, z + (1 - z) K_{eta, rho/(1 - z)}(B)},

the identity the arbitrary-law zero-quantile record used without a Lean
proof, and the same for every law alpha on [0, 1/2] with alpha{0} < 1, with
z = alpha{0} and eta its normalized positive part.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the two targets and three components with their types written out;
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

GROUP = "ZeroAtomSplit"
NAMES = ("Specification", "Support", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "6424f1c829ef114e84566a4b53013af2aa2b43ae1dc5c11fa74567a744ce326d"
TARGETS = {
    "ZeroAtomSplit.zero_atom_split": "ZeroAtomSplit.ZeroAtomSplitStatement",
    "ZeroAtomSplit.zero_atom_split_law": "ZeroAtomSplit.ZeroAtomSplitLawStatement",
}
COMPONENTS = (
    "ZeroAtomSplit.zeroSelection_add_zeroAtom",
    "ZeroAtomSplit.selection_smul",
    "ZeroAtomSplit.zeroSelection_zeroAtomLaw",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (z ρ B : ℝ),
    0 ≤ z → z < 1 → 0 < ρ → 0 < B →
    zeroSelection (zeroAtomLaw z η) ρ B =
      min (ENNReal.ofReal ρ)
        (ENNReal.ofReal z + ENNReal.ofReal (1 - z) * EntropyTail.selection η (ρ / (1 - z)) B) :=
  ZeroAtomSplit.zero_atom_split

example : ∀ (α : Measure ℝ) [IsProbabilityMeasure α] (ρ B : ℝ),
    α (Set.Icc 0 (1 / 2))ᶜ = 0 → zeroMass α < 1 → 0 < ρ → 0 < B →
    zeroSelection α ρ B =
      min (ENNReal.ofReal ρ)
        (ENNReal.ofReal (zeroMass α) +
          ENNReal.ofReal (1 - zeroMass α) *
            EntropyTail.selection (positiveLaw α) (ρ / (1 - zeroMass α)) B) :=
  ZeroAtomSplit.zero_atom_split_law

example : ∀ (ν : Measure ℝ) [IsFiniteMeasure ν] {z ρ B : ℝ}, 0 < ρ → 0 < B →
    zeroSelection (ENNReal.ofReal z • Measure.dirac 0 + ν) ρ B =
      min (ENNReal.ofReal ρ) (ENNReal.ofReal z + zeroSelection ν ρ B) :=
  @ZeroAtomSplit.zeroSelection_add_zeroAtom

example : ∀ (η : Measure Gap) [IsFiniteMeasure η] {c ρ : ℝ}, 0 < c → 0 ≤ ρ → ∀ (B : ℝ),
    EntropyTail.selection (ENNReal.ofReal c • η) ρ B =
      ENNReal.ofReal c * EntropyTail.selection η (ρ / c) B :=
  @ZeroAtomSplit.selection_smul

example : ∀ (η : Measure Gap) [IsFiniteMeasure η] {z ρ B : ℝ}, z < 1 → 0 < ρ → 0 < B →
    zeroSelection (zeroAtomLaw z η) ρ B =
      min (ENNReal.ofReal ρ)
        (ENNReal.ofReal z + ENNReal.ofReal (1 - z) * EntropyTail.selection η (ρ / (1 - z)) B) :=
  @ZeroAtomSplit.zeroSelection_zeroAtomLaw
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
        raise ValueError("Duplicate zero-atom split declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing zero-atom split target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed zero-atom split specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.ArbitraryLawAdaptation",
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
    print(f"All {len(TARGETS)} zero-atom split targets are certified")


if __name__ == "__main__":
    main()
