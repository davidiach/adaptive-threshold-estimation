"""Audit the remark that the bias subtraction cannot be uniformly reduced.

Proposition psi-null of v6 Appendix H bounds J_0(b) >= sup_h
(Psi(h) - 4b)_+^2 / (192 h^2) for 0 <= b <= rho/64. The remark after it takes
rho = 1/8, eps = 2^-10, mu = (1 - eps) delta_{1/2} + eps delta_d and
b = eps (1 - 2d)/4: the one-flip output X - b has bias at most b on the capped
class, null work one and variance at most 1/4, while Psi(d) >= eps. So for
every c < 4 and K > 0 the bound with c b and K in place of 4b and 192 fails at
h = d for every small enough gap d. The predicate refuted is Lean's
NullVarianceObstruction, the form in which J_0(b) >= J enters the transfers.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the target and four components with their types written out;
4. reports the transitive axioms of every public declaration in the directory.

With --replay the registered modules also go through the toolchain's
independent kernel checker. The statement was written after the proof; it is
pinned from this audit onward.
"""

from __future__ import annotations

import argparse
import re
import subprocess

from verify_blind_upper_components import FORBIDDEN, LEAN, sha, strip_comments, validate_reports
from verify_sharp_rms import public_names

GROUP = "BiasSubtraction"
NAMES = ("Specification", "Witness", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "1ececa4504ca40ab8473501b858e8a9d3243c0a403a15393207b4a025eda49f7"
TARGETS = {
    "BiasSubtraction.bias_subtraction": "BiasSubtraction.BiasSubtractionStatement",
}
COMPONENTS = (
    "BiasSubtraction.not_obstruction_of_gt",
    "BiasSubtraction.oneFlip_bias",
    "BiasSubtraction.remark_psi_lower",
    "BiasSubtraction.remarkLaw_probability",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : (∀ d : Gap, 0 ≤ remarkBias d ∧ remarkBias d ≤ (1/8)/64) ∧
    ∀ c : ℝ, c < 4 → ∀ K : ℝ, 0 < K → ∃ δ : ℝ, 0 < δ ∧ ∀ d : Gap, (d : ℝ) < δ →
      ¬ NullVarianceObstruction (remarkLaw d) (gapParameter false) (gapParameter true) (1/8)
        (remarkBias d)
        ((max ((rarePsi (remarkLaw d) (1/8) d).toReal - c*remarkBias d) 0)^2 /
          (K*(d : ℝ)^2)) :=
  BiasSubtraction.bias_subtraction

example : ∀ (d : Gap) (J : ℝ), 1/4 < J →
    ¬ NullVarianceObstruction (remarkLaw d) (gapParameter false) (gapParameter true) (1/8)
      (remarkBias d) J :=
  @BiasSubtraction.not_obstruction_of_gt

example : ∀ (d : Gap) (q : Gap → unitInterval), CappedPrior (remarkLaw d) (1/8) q →
    |populationMean (remarkLaw d) (Measure.dirac ()) (gapParameter false) (gapParameter true) q
      (oneFlipProcedure (remarkBias d)) - ∫ x, (q x : ℝ) ∂remarkLaw d| ≤ remarkBias d :=
  @BiasSubtraction.oneFlip_bias

example : ∀ (d : Gap), (d : ℝ) < 1/2 →
    ENNReal.ofReal (1/2^10) ≤ rarePsi (remarkLaw d) (1/8) d :=
  @BiasSubtraction.remark_psi_lower

example : ∀ (d : Gap), IsProbabilityMeasure (remarkLaw d) :=
  @BiasSubtraction.remarkLaw_probability
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
        raise ValueError("Duplicate bias-subtraction declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing bias-subtraction target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed bias-subtraction specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.ConfidenceLocalization ThresholdHC.ObservableSimulation ThresholdHC.RareAboveTwo ThresholdHC.BiasSubtraction",
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
    print("The bias-subtraction target is certified")


if __name__ == "__main__":
    main()
