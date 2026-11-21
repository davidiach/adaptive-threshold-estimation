"""Audit the restricted pilot correction of the population-step package.

The upper-bound note of research/2026-10-27-population-step (Theorem
thm:saddle and the theorem after it) fixes a scalar control variate: on the
rarity polytope Q, f(beta, q) = Var_q(Y - beta Z) has a saddle point, so a
fixed coefficient beta_0 gives an unbiased raw average with worst mean
squared error F*/n, where F* = inf_beta sup_q f, and no coefficient learned
by an independent pilot does better. The group states both for an abstract
mixture model of one fresh coin's observations (arbitrary conditional laws
given gap and sign), with mean squared errors in [0, infinity], and adds a
witness at the gap 1/2 with an internal fair coin where F* >= rho(1-rho) > 0.

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

GROUP = "PilotCorrection"
NAMES = ("Specification", "Quadratic", "Mixture", "Production", "CoinWitness", "Saddle", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "2ec262b5b2166a3d621a3aa97860f277e54b0b673e7cd011666f17bb4eadca98"
TARGETS = {
    "PilotCorrection.saddle": "PilotCorrection.SaddleStatement",
    "PilotCorrection.pilot_no_gain": "PilotCorrection.PilotNoGainStatement",
    "PilotCorrection.coin_witness": "PilotCorrection.CoinWitnessStatement",
}
COMPONENTS = (
    "PilotCorrection.fixedRisk_eq",
    "PilotCorrection.pilotRisk_eq",
    "PilotCorrection.saddle_real",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (Ω : Type) [MeasurableSpace Ω] (k : ℕ) (π : Fin k → ℝ) (ρ : ℝ)
    (Pplus Pminus : Fin k → Measure Ω)
    [∀ i, IsProbabilityMeasure (Pplus i)] [∀ i, IsProbabilityMeasure (Pminus i)]
    (Y Z : Ω → ℝ) (v : ℝ),
    FixedFeatures π ρ Pplus Pminus Y Z v →
    ∃ β₀ : ℝ, ∃ q₀ ∈ rarityPolytope π ρ,
      IsSaddlePointOn Set.univ (rarityPolytope π ρ)
        (fun β q => variance (fun ω => Y ω - β * Z ω) (coinLaw π Pplus Pminus q))
        β₀ q₀ ∧
      (⨅ β : ℝ, ⨆ q ∈ rarityPolytope π ρ,
          ((variance (fun ω => Y ω - β * Z ω) (coinLaw π Pplus Pminus q) : ℝ) :
            EReal)) =
        ((variance (fun ω => Y ω - β₀ * Z ω) (coinLaw π Pplus Pminus q₀) : ℝ) :
          EReal) ∧
      (⨆ q ∈ rarityPolytope π ρ, ⨅ β : ℝ,
          ((variance (fun ω => Y ω - β * Z ω) (coinLaw π Pplus Pminus q) : ℝ) :
            EReal)) =
        ((variance (fun ω => Y ω - β₀ * Z ω) (coinLaw π Pplus Pminus q₀) : ℝ) :
          EReal) :=
  PilotCorrection.saddle

example :
  ∀ (Ω : Type) [MeasurableSpace Ω] (k : ℕ) (π : Fin k → ℝ) (ρ : ℝ)
    (Pplus Pminus : Fin k → Measure Ω)
    [∀ i, IsProbabilityMeasure (Pplus i)] [∀ i, IsProbabilityMeasure (Pminus i)]
    (Y Z : Ω → ℝ) (v : ℝ),
    FixedFeatures π ρ Pplus Pminus Y Z v →
    ∃ β₀ Fstar : ℝ,
      (Fstar : EReal) = ⨅ β : ℝ, ⨆ q ∈ rarityPolytope π ρ,
        ((variance (fun ω => Y ω - β * Z ω) (coinLaw π Pplus Pminus q) : ℝ) :
          EReal) ∧
      ∀ n : ℕ, 1 ≤ n →
        (∀ q ∈ rarityPolytope π ρ,
          (∫ ω, rawAverage Y Z n β₀ ω
              ∂Measure.pi (fun _ : Fin n => coinLaw π Pplus Pminus q)) =
            signMass π q) ∧
        (⨆ q ∈ rarityPolytope π ρ, fixedRisk π Pplus Pminus Y Z n β₀ q) =
          ENNReal.ofReal (Fstar / n) ∧
        ∀ (T : Type) [MeasurableSpace T] (L : (Fin k → ℝ) → Measure T),
          (∀ q ∈ rarityPolytope π ρ, IsProbabilityMeasure (L q)) →
          ∀ βhat : T → ℝ, Measurable βhat →
            ENNReal.ofReal (Fstar / n) ≤
              ⨆ q ∈ rarityPolytope π ρ, pilotRisk π Pplus Pminus Y Z n L βhat q :=
  PilotCorrection.pilot_no_gain

example :
  ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 →
    let Pp : Fin 1 → Measure (Bool × Bool) := fun _ => (Measure.dirac true).prod fairCoin
    let Pm : Fin 1 → Measure (Bool × Bool) := fun _ => (Measure.dirac false).prod fairCoin
    let Y : Bool × Bool → ℝ := fun ω => if ω.1 then 1 else 0
    let Z : Bool × Bool → ℝ := fun ω => if ω.2 then 1 else -1
    (∀ i, IsProbabilityMeasure (Pp i)) ∧ (∀ i, IsProbabilityMeasure (Pm i)) ∧
    FixedFeatures (fun _ => 1) ρ Pp Pm Y Z 1 ∧
    ∃ q ∈ rarityPolytope (fun _ => 1) ρ, ∀ β : ℝ,
      ρ * (1 - ρ) ≤ variance (fun ω => Y ω - β * Z ω) (coinLaw (fun _ => 1) Pp Pm q) :=
  PilotCorrection.coin_witness

example : ∀ {Ω : Type} [MeasurableSpace Ω] {k : ℕ} {π : Fin k → ℝ} {ρ : ℝ}
    {Pplus Pminus : Fin k → Measure Ω} [∀ i, IsProbabilityMeasure (Pplus i)]
    [∀ i, IsProbabilityMeasure (Pminus i)] {Y Z : Ω → ℝ} {v : ℝ},
    FixedFeatures π ρ Pplus Pminus Y Z v → ∀ {q : Fin k → ℝ}, q ∈ rarityPolytope π ρ →
    ∀ (β : ℝ) {n : ℕ}, 1 ≤ n →
    fixedRisk π Pplus Pminus Y Z n β q =
      ENNReal.ofReal (variance (fun ω => Y ω - β * Z ω) (coinLaw π Pplus Pminus q) / n) :=
  @PilotCorrection.fixedRisk_eq

example : ∀ {Ω : Type} [MeasurableSpace Ω] {k : ℕ} {π : Fin k → ℝ} {ρ : ℝ}
    {Pplus Pminus : Fin k → Measure Ω} [∀ i, IsProbabilityMeasure (Pplus i)]
    [∀ i, IsProbabilityMeasure (Pminus i)] {Y Z : Ω → ℝ} {v : ℝ},
    FixedFeatures π ρ Pplus Pminus Y Z v → ∀ {q : Fin k → ℝ}, q ∈ rarityPolytope π ρ →
    ∀ {n : ℕ}, 1 ≤ n → ∀ {T : Type} [MeasurableSpace T] (L : (Fin k → ℝ) → Measure T)
    {βhat : T → ℝ}, Measurable βhat →
    pilotRisk π Pplus Pminus Y Z n L βhat q =
      ∫⁻ t, ENNReal.ofReal
        (variance (fun ω => Y ω - βhat t * Z ω) (coinLaw π Pplus Pminus q) / n) ∂L q :=
  @PilotCorrection.pilotRisk_eq

example : ∀ {Ω : Type} [MeasurableSpace Ω] {k : ℕ} {π : Fin k → ℝ} {ρ : ℝ}
    {Pplus Pminus : Fin k → Measure Ω} [∀ i, IsProbabilityMeasure (Pplus i)]
    [∀ i, IsProbabilityMeasure (Pminus i)] {Y Z : Ω → ℝ} {v : ℝ},
    FixedFeatures π ρ Pplus Pminus Y Z v →
    ∃ β₀ : ℝ, ∃ q₀ ∈ rarityPolytope π ρ,
      IsSaddlePointOn Set.univ (rarityPolytope π ρ)
        (fun β q => variance (fun ω => Y ω - β * Z ω) (coinLaw π Pplus Pminus q)) β₀ q₀ :=
  @PilotCorrection.saddle_real
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
        raise ValueError("Duplicate pilot-correction declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing pilot-correction target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed pilot-correction specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.PilotCorrection",
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
    print(f"All {len(TARGETS)} pilot-correction targets are certified")


if __name__ == "__main__":
    main()
