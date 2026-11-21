"""Audit the weighted sign entropy with the paper's coefficient 214.

Lemma lem:weighted-sign of the v6 lower-bound foundations appendix (display
eq:sc-weighted-sign): for one observable sign test with a common seed law,
error at most 1/10 for both signs at gaps 0 < d_j <= 1/128 separated by a
factor two, and finite negative-sign work, 1 + Ent(pi) <= 214 sum_j pi_j c_j
with c_j = d_j^2 E_{-d_j} tau, here in homogeneous form for every nonnegative
weight vector. The group also proves the two steps of the paper's proof: the
per-gap floor c_j > 3/40 and the pathwise overlap 25/3 of the stopping
windows. The locked target EntropyTailLower.WeightedSignEntropyStatement, with
the same binders, carries the weaker coefficient 4096; it is unchanged.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the three targets and three components with their types written out;
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

GROUP = "WeightedSignSharp"
NAMES = ("Specification", "CappedSign", "SignFloor", "SharpOverlap", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "325787a80fee46400c63ae0869544abef88b585accb6db6dbc941f32e80794c4"
TARGETS = {
    "WeightedSignSharp.sign_work_floor": "WeightedSignSharp.SignWorkFloorStatement",
    "WeightedSignSharp.window_overlap": "WeightedSignSharp.WindowOverlapStatement",
    "WeightedSignSharp.weighted_sign_entropy_214": "WeightedSignSharp.WeightedSignEntropy214Statement",
}
COMPONENTS = (
    "WeightedSignSharp.log_twenty_five_thirds_le",
    "WeightedSignSharp.binary_kl_four_fifths",
    "WeightedSignSharp.capped_geometric_sum",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ {R : Type} [MeasurableSpace R] (ν : Measure R) [IsProbabilityMeasure ν]
    (A : SignTest R) (d : EntropyGap),
    expectedSignTestWork ν (signParameter d false) A ≠ ∞ →
    (ν.prod (Tier2.tapeMeasure (signParameter d false))).real {z | A.output z = true} ≤ 1/10 →
    (ν.prod (Tier2.tapeMeasure (signParameter d true))).real {z | A.output z = false} ≤ 1/10 →
    (3/40 : ℝ) < (d : ℝ)^2 * (expectedSignTestWork ν (signParameter d false) A).toReal :=
  WeightedSignSharp.sign_work_floor

example :
  ∀ {R : Type} [MeasurableSpace R] (ν : Measure R) (A : SignTest R) (K : ℕ)
    (d : Fin K → EntropyGap),
    (∀ i j, j.val = i.val + 1 → 2 * (d j : ℝ) ≤ (d i : ℝ)) →
    ∀ z : R × (ℕ → Bool),
      (∑ i, (signTestWindow A (entropyLowerTime (d i))
        (entropyUpperTime (expectedSignTestWork ν (signParameter (d i) false) A).toReal)).indicator
          (fun _ => 1 / (1 + (d i : ℝ)^2 *
            (expectedSignTestWork ν (signParameter (d i) false) A).toReal)) z) ≤ 25/3 :=
  WeightedSignSharp.window_overlap

example :
  ∀ {R : Type} [MeasurableSpace R] (ν : Measure R) [IsProbabilityMeasure ν]
    (A : SignTest R) (K : ℕ) (d : Fin K → EntropyGap),
    (∀ i j, j.val = i.val + 1 → 2 * (d j : ℝ) ≤ (d i : ℝ)) →
    (∀ i, expectedSignTestWork ν (signParameter (d i) false) A ≠ ∞) →
    (∀ i b, (ν.prod (Tier2.tapeMeasure (signParameter (d i) b))).real
      {z | A.output z ≠ b} ≤ 1 / 10) →
    ∀ a : Fin K → ℝ, (∀ i, 0 ≤ a i) →
      ThresholdHC.EntropyTailQuantile.costEntropy a ≤
        214 * ∑ i, a i * ((d i : ℝ)^2 *
          (expectedSignTestWork ν (signParameter (d i) false) A).toReal) :=
  WeightedSignSharp.weighted_sign_entropy_214

example : Real.log (25/3 : ℝ) ≤ 87/40 :=
  WeightedSignSharp.log_twenty_five_thirds_le

example : (9/5) * Real.log 2 ≤ klB (4/5) (1/10) :=
  WeightedSignSharp.binary_kl_four_fifths

example : ∀ M : ℕ, (∑ n ∈ Finset.range M, min 1 (16384 * (1/4 : ℝ)^n)) ≤ 25/3 :=
  WeightedSignSharp.capped_geometric_sum
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
        raise ValueError("Duplicate weighted-sign-sharp declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing weighted-sign-sharp target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed weighted-sign-sharp specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open InformationTheory ThresholdHC ThresholdHC.CriticalEntropy ThresholdHC.WeightedSignSharp",
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
    print(f"All {len(TARGETS)} weighted-sign-sharp targets are certified")


if __name__ == "__main__":
    main()
