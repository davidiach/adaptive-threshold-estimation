"""Audit the population class and the G-form of the target.

The model of sec:model in the v6 manuscript defines the population class
G(mu) = {G_{mu,q} : q measurable} through D ~ mu, S | D ~ Ber(q(D)) and
P = 1/2 + (2S-1)D, and the introduction writes the target as
theta(G) = P_G(P > 1/2) with mu the law of |P - 1/2|. The model-fidelity
guide asks for the converse: every law G of P with |P - 1/2| ~ mu is some
G_{mu,q}. The group proves that every G_{mu,q} has magnitude law mu, the
converse through a Radon-Nikodym density, the resulting description of G(mu)
as exactly the laws of P on [0,1] with |P - 1/2| ~ mu, and theta = P_G(P > 1/2)
for every sign law representing G. The magnitude law is read on R, so the
headline statements have no default value; the risk theorems are not
restated in G-form.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the four targets and three components with their types written out;
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

GROUP = "LatentDisintegration"
NAMES = ("Specification", "Magnitude", "Disintegration", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "c61c25361eccdb15896f718fcd7fec5b4a8b3aa4eb75bdd28377f939d900b4a5"
TARGETS = {
    "LatentDisintegration.latent_magnitude": "LatentDisintegration.LatentMagnitudeStatement",
    "LatentDisintegration.latent_disintegration": "LatentDisintegration.DisintegrationStatement",
    "LatentDisintegration.population_class": "LatentDisintegration.PopulationClassStatement",
    "LatentDisintegration.g_form_target": "LatentDisintegration.GFormTargetStatement",
}
COMPONENTS = (
    "LatentDisintegration.gapOf_coe",
    "LatentDisintegration.latent_gapOf_magnitude",
    "LatentDisintegration.measurable_gapOf",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (latentLaw μ q).map (fun p : unitInterval => |(p : ℝ) - 1/2|) = μ.map Subtype.val :=
  LatentDisintegration.latent_magnitude

example :
  ∀ (G : Measure unitInterval) [IsProbabilityMeasure G],
    G {p : unitInterval | (p : ℝ) = 1/2} = 0 → ∃ q : SignLaw, latentLaw (G.map gapOf) q = G :=
  LatentDisintegration.latent_disintegration

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (G : Measure unitInterval),
    (∃ q : SignLaw, latentLaw μ q = G) ↔
      G.map (fun p : unitInterval => |(p : ℝ) - 1/2|) = μ.map Subtype.val :=
  LatentDisintegration.population_class

example :
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (G : Measure unitInterval),
    G.map (fun p : unitInterval => |(p : ℝ) - 1/2|) = μ.map Subtype.val →
      (∃ q : SignLaw, latentLaw μ q = G) ∧
      ∀ q : SignLaw, latentLaw μ q = G →
        signMean μ q.val = G.real {p : unitInterval | (1/2 : ℝ) < p} :=
  LatentDisintegration.g_form_target

example : ∀ (p : unitInterval), (p : ℝ) ≠ 1/2 → (gapOf p : ℝ) = |(p : ℝ) - 1/2| :=
  LatentDisintegration.gapOf_coe

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (latentLaw μ q).map gapOf = μ ∧ latentLaw μ q {p : unitInterval | (p : ℝ) = 1/2} = 0 :=
  LatentDisintegration.latent_gapOf_magnitude

example : Measurable gapOf :=
  LatentDisintegration.measurable_gapOf
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
        raise ValueError("Duplicate latent-disintegration declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing latent-disintegration target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed latent-disintegration specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.SmoothDensity ThresholdHC.LatentDisintegration",
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
    print(f"All {len(TARGETS)} latent-disintegration targets are certified")


if __name__ == "__main__":
    main()
