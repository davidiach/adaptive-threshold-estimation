"""Audit the horizon-eight finite-prior Bayes allocation example.

The population-step research package solves finite-horizon Bayes allocation
problems exactly for two atomic gap laws with uniform priors over locked sign
laws, and reports that the adaptive dynamic-program policy beats every
fresh-only and every single-coin design at horizon eight. The group states, in
the original population experiment, that an explicit eight-flip adaptive
witness (the stored policy as a label table, with the posterior-mean output)
has Bayes squared error below the two fixed designs' minimum by at least
1.5917 percent (two scales) and 5.0307 percent (three scales), with the upper,
lower and tightness constants rounded at 10^-15. It does not state that the
witness is the adaptive minimum.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification, which inlines both 256-entry policy tables;
3. restates the nine targets and three components with their types written out;
4. reports the transitive axioms of every public declaration in the directory.

With --replay the registered modules also go through the toolchain's
independent kernel checker. The statements were written before the proofs
and reviewed before the pin; they are pinned from this audit onward.
"""

from __future__ import annotations

import argparse
import re
import subprocess

from verify_blind_upper_components import FORBIDDEN, LEAN, sha, strip_comments, validate_reports
from verify_sharp_rms import public_names

GROUP = "FiniteBayesAllocation"
NAMES = ("Specification", "Kernel", "CertTwo", "CertThree", "Weight", "Risk", "Atoms", "Posterior", "Bayes", "Cases", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "6700211d7142de359d46213ce420a87632365b383cc61cf09ae3bd88561e6bda"
TARGETS = {
    "FiniteBayesAllocation.two_scales_upper": "FiniteBayesAllocation.TwoScalesUpperStatement",
    "FiniteBayesAllocation.three_scales_upper": "FiniteBayesAllocation.ThreeScalesUpperStatement",
    "FiniteBayesAllocation.restricted_lower": "FiniteBayesAllocation.RestrictedLowerStatement",
    "FiniteBayesAllocation.two_scales_restricted_tight": "FiniteBayesAllocation.TwoScalesRestrictedTightStatement",
    "FiniteBayesAllocation.three_scales_restricted_tight": "FiniteBayesAllocation.ThreeScalesRestrictedTightStatement",
    "FiniteBayesAllocation.two_scales_gain": "FiniteBayesAllocation.TwoScalesGainStatement",
    "FiniteBayesAllocation.three_scales_gain": "FiniteBayesAllocation.ThreeScalesGainStatement",
    "FiniteBayesAllocation.two_scales_pinned_gain": "FiniteBayesAllocation.TwoScalesPinnedGainStatement",
    "FiniteBayesAllocation.three_scales_pinned_gain": "FiniteBayesAllocation.ThreeScalesPinnedGainStatement",
}
COMPONENTS = (
    "FiniteBayesAllocation.two_adaptive_cert",
    "FiniteBayesAllocation.two_table_upper",
    "FiniteBayesAllocation.two_fresh_lower",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∃ A : AdaptiveEstimator Unit, (∀ r, A.policy r = stopAt 8 (tableLabel twoScalesTable)) ∧
    PathwiseCap A 8 ∧ bayesRisk twoScalesLaw twoScalesSign A ≤ ENNReal.ofReal (2111783001239 / 10^15) :=
  FiniteBayesAllocation.two_scales_upper

example :
  ∃ A : AdaptiveEstimator Unit, (∀ r, A.policy r = stopAt 8 (tableLabel threeScalesTable)) ∧
    PathwiseCap A 8 ∧
    bayesRisk threeScalesLaw threeScalesSign A ≤ ENNReal.ofReal (1706729084112 / 10^15) :=
  FiniteBayesAllocation.three_scales_upper

example :
  ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R),
    (FreshDesign A →
      ENNReal.ofReal (2149143352671 / 10^15) ≤ bayesRisk twoScalesLaw twoScalesSign A ∧
      ENNReal.ofReal (1797138065871 / 10^15) ≤ bayesRisk threeScalesLaw threeScalesSign A) ∧
    (SingleDesign A →
      ENNReal.ofReal (2145940859276 / 10^15) ≤ bayesRisk twoScalesLaw twoScalesSign A ∧
      ENNReal.ofReal (1868722055075 / 10^15) ≤ bayesRisk threeScalesLaw threeScalesSign A) :=
  FiniteBayesAllocation.restricted_lower

example :
  (∃ A : AdaptiveEstimator Unit, FreshDesign A ∧
     bayesRisk twoScalesLaw twoScalesSign A ≤ ENNReal.ofReal (2149143352672 / 10^15)) ∧
  (∃ A : AdaptiveEstimator Unit, SingleDesign A ∧
     bayesRisk twoScalesLaw twoScalesSign A ≤ ENNReal.ofReal (2145940859277 / 10^15)) :=
  FiniteBayesAllocation.two_scales_restricted_tight

example :
  (∃ A : AdaptiveEstimator Unit, FreshDesign A ∧
     bayesRisk threeScalesLaw threeScalesSign A ≤ ENNReal.ofReal (1797138065872 / 10^15)) ∧
  (∃ A : AdaptiveEstimator Unit, SingleDesign A ∧
     bayesRisk threeScalesLaw threeScalesSign A ≤ ENNReal.ofReal (1868722055076 / 10^15)) :=
  FiniteBayesAllocation.three_scales_restricted_tight

example :
  ∃ W : AdaptiveEstimator Unit, (∃ p : List Bool → ℕ, ∀ r, W.policy r = stopAt 8 p) ∧
    ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R), FreshDesign A ∨ SingleDesign A →
      bayesRisk twoScalesLaw twoScalesSign W ≤
        ENNReal.ofReal (1 - 15917 / 1000000) * bayesRisk twoScalesLaw twoScalesSign A :=
  FiniteBayesAllocation.two_scales_gain

example :
  ∃ W : AdaptiveEstimator Unit, (∃ p : List Bool → ℕ, ∀ r, W.policy r = stopAt 8 p) ∧
    ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R), FreshDesign A ∨ SingleDesign A →
      bayesRisk threeScalesLaw threeScalesSign W ≤
        ENNReal.ofReal (1 - 50307 / 1000000) * bayesRisk threeScalesLaw threeScalesSign A :=
  FiniteBayesAllocation.three_scales_gain

example :
  ∃ W : AdaptiveEstimator Unit, (∀ r, W.policy r = stopAt 8 (tableLabel twoScalesTable)) ∧
    PathwiseCap W 8 ∧
    ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R), FreshDesign A ∨ SingleDesign A →
      bayesRisk twoScalesLaw twoScalesSign W ≤
        ENNReal.ofReal (1 - 15917 / 1000000) * bayesRisk twoScalesLaw twoScalesSign A :=
  FiniteBayesAllocation.two_scales_pinned_gain

example :
  ∃ W : AdaptiveEstimator Unit, (∀ r, W.policy r = stopAt 8 (tableLabel threeScalesTable)) ∧
    PathwiseCap W 8 ∧
    ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R), FreshDesign A ∨ SingleDesign A →
      bayesRisk threeScalesLaw threeScalesSign W ≤
        ENNReal.ofReal (1 - 50307 / 1000000) * bayesRisk threeScalesLaw threeScalesSign A :=
  FiniteBayesAllocation.three_scales_pinned_gain

example : FiniteBayesAllocation.certify (FiniteBayesAllocation.scaleOf FiniteBayesAllocation.twoCode) (FiniteBayesAllocation.run FiniteBayesAllocation.twoCode (FiniteBayesAllocation.tableLabel FiniteBayesAllocation.twoScalesTable)) = (1267069800743260913, 1267069800743261169, true) :=
  FiniteBayesAllocation.two_adaptive_cert

example : FiniteBayesAllocation.bayesRisk FiniteBayesAllocation.twoScalesLaw FiniteBayesAllocation.twoScalesSign (FiniteBayesAllocation.postEstimator FiniteBayesAllocation.twoCode (FiniteBayesAllocation.tableLabel FiniteBayesAllocation.twoScalesTable)) ≤ ENNReal.ofReal (2111783001239 / 10^15) :=
  FiniteBayesAllocation.two_table_upper

example : ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R), FiniteBayesAllocation.FreshDesign A → ENNReal.ofReal (2149143352671 / 10^15) ≤ FiniteBayesAllocation.bayesRisk FiniteBayesAllocation.twoScalesLaw FiniteBayesAllocation.twoScalesSign A :=
  @FiniteBayesAllocation.two_fresh_lower
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
        raise ValueError("Duplicate finite-bayes-allocation declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing finite-bayes-allocation target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed finite-bayes-allocation specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.FiniteLawCertificates ThresholdHC.FiniteBayesAllocation",
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
    print(f"All {len(TARGETS)} finite-bayes-allocation targets are certified")


if __name__ == "__main__":
    main()
