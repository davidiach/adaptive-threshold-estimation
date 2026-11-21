"""Audit the upper end of the sharp quantile factor.

Theorem thm:sharp-quantile-factor of the v6 paper (appendix-optimal-factor.tex)
says that exactly one k in [sqrt 2, 31/20] has max_{1<=u<=31/20} F(k, u) = 1,
that it is the sharp comparison factor c_* for general and for finite laws,
and that 1.462554551279 < c_* < 1.462554551280. The lower end and the
characterization were Lean-checked; the upper end had an exact rational
certificate in Python only. The group proves the upper end by a bisection
cover of [1, 31/20] whose cells are checked by decide +kernel on natural
numbers, with a truncation of the series after five terms and a convexity
bound, and states the whole theorem.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the four targets and three components with their types written out;
4. reports the transitive axioms of every public declaration in the directory.

With --replay the registered modules also go through the toolchain's
independent kernel checker, which re-evaluates the four certificate quarters.
The statements were written after the proofs; they are pinned from this
audit onward.
"""

from __future__ import annotations

import argparse
import re
import subprocess

from verify_blind_upper_components import FORBIDDEN, LEAN, sha, strip_comments, validate_reports
from verify_sharp_rms import public_names

GROUP = "QuantileFactorUpper"
NAMES = ("Specification", "Checker", "Truncation", "Convexity", "ExpEnclosure", "Cover", "Certificate", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "e8d8336e6ae53aef89582cc207125483ef6f8f39db9029169ba828dedb4c7eb6"
TARGETS = {
    "QuantileFactorUpper.peak_upper": "QuantileFactorUpper.PeakUpperStatement",
    "QuantileFactorUpper.root_upper": "QuantileFactorUpper.RootUpperStatement",
    "QuantileFactorUpper.root_bracket": "QuantileFactorUpper.RootBracketStatement",
    "QuantileFactorUpper.sharp_quantile_factor": "QuantileFactorUpper.SharpQuantileFactorStatement",
}
COMPONENTS = (
    "QuantileFactorUpper.certify_full",
    "QuantileFactorUpper.partitionSeries_lt_one",
    "QuantileFactorUpper.partitionSeries_le_truncation",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  scalarPeak (1462554551280/1000000000000) < 1 :=
  QuantileFactorUpper.peak_upper

example :
  scalarRoot < (1462554551280/1000000000000 : ℝ) :=
  QuantileFactorUpper.root_upper

example :
  (1462554551279/1000000000000 : ℝ) < scalarRoot ∧
    scalarRoot < (1462554551280/1000000000000 : ℝ) :=
  QuantileFactorUpper.root_bracket

example :
  ∃ c : ℝ, c ∈ Set.Icc (sqrt 2) (31/20) ∧
    IsGreatest (partitionSeries c '' Set.Icc 1 (31/20)) 1 ∧
    (∀ k ∈ Set.Icc (sqrt 2) (31/20),
      IsGreatest (partitionSeries k '' Set.Icc 1 (31/20)) 1 → k = c) ∧
    (∀ k : ℝ, (UniversalFactor k ↔ c ≤ k) ∧ (FiniteUniversalFactor k ↔ c ≤ k)) ∧
    (1462554551279/1000000000000 : ℝ) < c ∧ c < 1462554551280/1000000000000 :=
  QuantileFactorUpper.sharp_quantile_factor

example : certify 24 gridDen gridTop = true :=
  QuantileFactorUpper.certify_full

example : ∀ {u : ℝ}, u ∈ Set.Icc (1 : ℝ) (31/20) →
    partitionSeries (1462554551280/1000000000000) u < 1 :=
  @QuantileFactorUpper.partitionSeries_lt_one

example : ∀ {k u : ℝ}, sqrt 2 ≤ k → 1 ≤ u →
    partitionSeries k u ≤ finitePartition 5 k u + 1/2^62 :=
  @QuantileFactorUpper.partitionSeries_le_truncation
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
        raise ValueError("Duplicate quantile-factor-upper declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing quantile-factor-upper target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed quantile-factor-upper specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open Real ThresholdHC ThresholdHC.OptimalQuantile ThresholdHC.QuantileOptimality ThresholdHC.QuantileFactorUpper",
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
    print(f"All {len(TARGETS)} quantile-factor-upper targets are certified")


if __name__ == "__main__":
    main()
