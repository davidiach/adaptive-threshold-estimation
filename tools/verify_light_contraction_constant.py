"""Audit the constant C_V of the light random contraction.

The arbitrary-law adaptation section of the v6 paper (display (UA4), and (A4)
of docs/ARBITRARY_LAW_ADAPTATION.md) bounds the cost entropy of a random
contraction V with distribution function G_V(v) = 2 exp(-1/(2 v^2)) below 1/4
through the series C_V = sum_{k>=2} 4^(k+1) p_k [1 + log(1/p_k) + log 2] of its
dyadic band masses p_k, and states p_2 = 1 - 2 exp(-32), p_k <= 2 exp(-4^k/2)
for k >= 3, a first summand below 192, C_V < 256, E V^-2 <= C_V and
E V^-1 <= 16. The group checks these for every law with that distribution
function and for the constructed multiplier, and the sharper C_V <= 1024/5 as
a component. The entropy inequality of (UA4) itself is not stated.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the six targets and three components with their types written out;
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

GROUP = "LightContractionConstant"
NAMES = ("Specification", "Masses", "Series", "Moments", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "9063d0bd83a0ecea4d6bea7991880b74a08ddecc73f36e4aafe186db922a9665"
TARGETS = {
    "LightContractionConstant.first_band_mass": "LightContractionConstant.FirstBandStatement",
    "LightContractionConstant.tail_band_mass": "LightContractionConstant.TailBandStatement",
    "LightContractionConstant.first_term_bound": "LightContractionConstant.FirstTermStatement",
    "LightContractionConstant.light_cv_bound": "LightContractionConstant.LightCVStatement",
    "LightContractionConstant.light_moment_bounds": "LightContractionConstant.LightMomentStatement",
    "LightContractionConstant.constructed_light_cv": "LightContractionConstant.ConstructedLightCVStatement",
}
COMPONENTS = (
    "LightContractionConstant.cvTerm_tail_le",
    "LightContractionConstant.cvTerm_le_geometric",
    "LightContractionConstant.lightCV_le",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (ν : Measure Gap) [IsProbabilityMeasure ν],
    (∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) →
    bandProb ν 2 = 1 - 2 * Real.exp (-32) :=
  LightContractionConstant.first_band_mass

example :
  ∀ (ν : Measure Gap) [IsProbabilityMeasure ν],
    (∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) →
    ∀ k : ℕ, 3 ≤ k → bandProb ν k ≤ 2 * Real.exp (-((4 : ℝ)^k / 2)) :=
  LightContractionConstant.tail_band_mass

example :
  ∀ (ν : Measure Gap) [IsProbabilityMeasure ν],
    (∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) →
    cvTerm ν 2 < 192 :=
  LightContractionConstant.first_term_bound

example :
  ∀ (ν : Measure Gap) [IsProbabilityMeasure ν],
    (∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) →
    Summable (fun j : ℕ => cvTerm ν (j+2)) ∧ lightCV ν < 256 :=
  LightContractionConstant.light_cv_bound

example :
  ∀ (ν : Measure Gap) [IsProbabilityMeasure ν],
    (∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) →
    (∫⁻ v, ENNReal.ofReal (((v : ℝ)⁻¹)^2) ∂ν) ≤ ENNReal.ofReal (lightCV ν) ∧
    (∫⁻ v, ENNReal.ofReal (((v : ℝ)⁻¹)^2) ∂ν) ≤ 256 ∧
    (∫⁻ v, ENNReal.ofReal ((v : ℝ)⁻¹) ∂ν) ≤ 16 :=
  LightContractionConstant.light_moment_bounds

example :
  bandProb lightMultiplier 2 = 1 - 2 * Real.exp (-32) ∧
  Summable (fun j : ℕ => cvTerm lightMultiplier (j+2)) ∧ lightCV lightMultiplier < 256 :=
  LightContractionConstant.constructed_light_cv

example : ∀ (ν : Measure Gap), (∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) →
    ∀ (n : ℕ), 1 ≤ n → cvTerm ν (n+2) ≤ 12 * (1/16 : ℝ)^n :=
  LightContractionConstant.cvTerm_tail_le

example : ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], (∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) →
    ∀ (j : ℕ), cvTerm ν (j+2) ≤ 192 * (1/16 : ℝ)^j :=
  LightContractionConstant.cvTerm_le_geometric

example : ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], (∀ x : ℝ, ν {v : Gap | (v : ℝ) ≤ x} = ENNReal.ofReal (lightCDF x)) →
    lightCV ν ≤ 1024/5 :=
  LightContractionConstant.lightCV_le
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
        raise ValueError("Duplicate light-contraction-constant declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing light-contraction-constant target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed light-contraction-constant specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.ArbitraryLawAdaptation ThresholdHC.LightContractionConstant",
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
    print(f"All {len(TARGETS)} light-contraction-constant targets are certified")


if __name__ == "__main__":
    main()
