"""Audit the sharp universal RMS lower coefficient and its oracle forms.

For every gap law and every budget at least one, minimax RMS risk is at least
one sixth of the modulus, and one sixth is the largest such coefficient. The
same holds when every magnitude is revealed and when the algorithm selects
each fresh magnitude. The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification, whose eight statements use only the original
   experiment, risk and modulus definitions;
3. restates the eight targets and thirty component theorems with their types
   written out, so a changed statement cannot pass under an old name;
4. reports the transitive axioms of every public declaration in the directory.

The proofs keep helper lemmas private. A private declaration has no name an
audit source can cite, so it is not a root here; the whole-project audit
(`verify_project_axioms.py`) checks the axioms of every constant, private ones
included. With --replay the registered modules also go through the
toolchain's independent kernel checker, which re-evaluates the 140 integer
comparisons of the intermediate budget window.

The statements were written after the proofs, from the research checkpoint
`research/2026-11-17-rms-constants`; they are pinned from this audit onward.
"""
from __future__ import annotations

import argparse
import re
import subprocess

from verify_blind_upper_components import (
    ANY_DECLARATION, DECLARATION, FORBIDDEN, LEAN, sha, strip_comments, validate_reports,
)

PREFIX = "ThresholdHC.SharpRMS."
SOURCES = LEAN / "ThresholdHC/SharpRMS"
MODULES = (
    "Specification", "Attainment", "Entropy", "Transcript", "Information", "PrefixCost",
    "WeakRisk", "WeakPopulation", "Simulation", "SmallBudget", "SmallPrefix",
    "BayesBudget", "FourBudget", "Score", "Fisher", "Barrier", "AdaptivePrice",
    "PriceBounds", "CriticalBudget", "GridArithmetic", "WindowBound", "WindowPart1",
    "WindowPart2", "WindowPart3", "WindowPart4", "WindowPart5", "WindowPart6",
    "WindowPart7", "Window", "WindowReal", "Interpolation", "Rectangles", "GridPrices",
    "GridIntegral", "GridSum", "MiddleBudget", "Heterogeneous", "WordSimulation",
    "AdaptiveSimulation", "Causal", "ArrayLaw", "TapeLaw", "TapeMixture", "SingleTape",
    "PopulationTransfer", "Reduction", "Unrestricted", "OracleTapes", "OracleLaw",
    "OracleReduction", "OracleBounds", "FreshLabels", "OracleAttainment", "Full",
)
SPEC_HASH = "29858340e7d3d937aa6ce1d2b0e9060f85199cc207fecc74982274ed6b71e2b4"
TARGETS = {
    "sharp_lower": "SharpLowerStatement",
    "sharp_coefficient": "SharpCoefficientStatement",
    "sharp_endpoint": "SharpEndpointStatement",
    "large_budget_lower": "LargeBudgetLowerStatement",
    "gap_reduction": "GapReductionStatement",
    "oracle_sharp_lower": "OracleSharpLowerStatement",
    "oracle_large_budget_lower_bound": "OracleLargeBudgetLowerStatement",
    "oracle_endpoint": "OracleEndpointStatement",
}
COMPONENTS = (
    "four_flips_budget", "four_flips_squared_risk", "endpoint_minimax_upper",
    "three_bias_risk", "creation_tilt", "creation_wald", "creation_paired_cost",
    "weak_gap_minimax_lower", "critical_step_kernel", "posterior_lattice_gap",
    "four_budget_minimax_lower", "endpoint_minimax_eq", "adaptive_fisher_price",
    "near_perfect_integral", "minimax_from_tapered_price", "near_perfect_minimax_lower",
    "checked_window", "real_window", "middle_minimax_lower", "critical_minimax_lower",
    "unrestricted_minimax_lower", "universal_coefficient_iff",
    "large_budget_minimax_lower", "critical_gap_reduction", "simulation_expected_work",
    "simulation_rms", "oracle_minimax_lower", "oracle_large_budget_lower",
    "oracle_endpoint_eq", "oracle_gap_reduction",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)
NAMESPACE = re.compile(r"^namespace\s+([\w.]+)\s*$", re.M)
PRIVATE = re.compile(r"\bprivate\b")

EXACT = """
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) ≤ minimaxRisk μ B := sharp_lower

example : ∀ c : ℝ, (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤ minimaxRisk μ B) ↔ c ≤ 1/6 := sharp_coefficient

example : minimaxRisk (Measure.dirac (⟨1/2, by norm_num⟩ : Gap)) 4 = ENNReal.ofReal (1/6 : ℝ) :=
  sharp_endpoint

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * Real.sqrt (59/2100 : ℝ)) ≤ minimaxRisk μ B :=
  large_budget_lower

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (g : Gap) (B : ℝ),
    ENNReal.ofReal (modulus μ g.val) * minimaxRisk (Measure.dirac g) B ≤ minimaxRisk μ B :=
  gap_reduction

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) ≤ selectedMinimaxRisk μ B := oracle_sharp_lower

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25 ≤ B →
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * Real.sqrt (59/2100 : ℝ)) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * Real.sqrt (59/2100 : ℝ)) ≤ selectedMinimaxRisk μ B :=
  oracle_large_budget_lower_bound

example : revealedMinimaxRisk (Measure.dirac (⟨1/2, by norm_num⟩ : Gap)) 4 = ENNReal.ofReal (1/6 : ℝ) ∧
    selectedMinimaxRisk (Measure.dirac (⟨1/2, by norm_num⟩ : Gap)) 4 = ENNReal.ofReal (1/6 : ℝ) :=
  oracle_endpoint

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], UniformBudget μ fourFlips 4 :=
  @four_flips_budget

example : ∀ q : SignLaw, squaredRisk (experimentLaw (Measure.dirac endpointGap) fourFlips q)
    (populationOutput fourFlips) (signMean (Measure.dirac endpointGap) q.val) =
    ENNReal.ofReal (1/36 : ℝ) := four_flips_squared_risk

example : minimaxRisk (Measure.dirac endpointGap) 4 ≤ ENNReal.ofReal (1/6:ℝ) :=
  endpoint_minimax_upper

example : ∀ {Ω : Type} [MeasurableSpace Ω] (P Qp Qm : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Qp] [IsProbabilityMeasure Qm]
    (X : Ω → ℝ), Measurable X →
    klDiv P Qp + klDiv P Qm ≤ ENNReal.ofReal (2*3283/3150:ℝ) →
    ENNReal.ofReal (1/9:ℝ) ≤ max (squaredRisk P X 0)
      (max (squaredRisk Qp X (7/10)) (squaredRisk Qm X (-(7/10)))) :=
  @three_bias_risk

example : ∀ {n : ℕ} (pol : List Bool → Option ℕ) (w : Prefix n) (d t : ℕ → ℝ),
    (∀ i, 0 ≤ d i ∧ d i ≤ 1/2) →
    creationLaw pol d (fun i => (1+t i)/2) w =
      creationLaw pol d (fun _ => 1/2) w *
        ∏ i : Fin (coinCap n pol), (1+t i.val*
          posterior (capPolicy (coinCap n pol) pol) w (fun j => d j.val) i) :=
  @creation_tilt

example : ∀ {n : ℕ} (pol : List Bool → Option ℕ) (s : ℝ), 0 ≤ s → s ≤ 1 →
    (∑ w : Prefix n, creationLaw pol (fun _ => s/2) (fun _ => 1/2) w *
      ∑ i : Fin (coinCap n pol), posterior (capPolicy (coinCap n pol) pol) w (fun _ => s/2) i *
        netCount (capPolicy (coinCap n pol) pol) w i) =
      s * ∑ w : Prefix n, creationLaw pol (fun _ => s/2) (fun _ => 1/2) w * workOf w :=
  @creation_wald

example : ∀ {n : ℕ} (pol : List Bool → Option ℕ) (s B : ℝ),
    0 < s → s ≤ 2/5 → s^2*B = 4 →
    (∑ w : Prefix n, creationLaw pol (fun _ => s/2) (fun _ => 1/2) w * workOf w) ≤ B →
    pairedCost (n := n) (creationLaw pol (fun _ => s/2) (fun _ => 1/2))
      (creationLaw pol (fun _ => s/2) (fun _ => (1+7/10)/2))
      (creationLaw pol (fun _ => s/2) (fun _ => (1+ -(7/10))/2)) ≤ 2*3283/3150 :=
  @creation_paired_cost

example : ∀ (g : Gap) (B : ℝ), 2*g.val ≤ 2/5 → (2*g.val)^2*B = 4 →
    ENNReal.ofReal (Real.sqrt (59/2100:ℝ)) ≤ minimaxRisk (Measure.dirac g) B :=
  weak_gap_minimax_lower

example : ∀ (a s z : ℝ), 0 < s → s < a → |z| ≤ 1 → (z=0 ∨ a ≤ |z|) →
    let f := s/a
    let c := copyProbability f z
    0 ≤ c ∧ c ≤ 1 ∧ |fallbackMean a z| ≤ 1 ∧
      ∀ e : ℝ, (e = -1 ∨ e = 1) →
        c*(s*e)+(1-c)*fallbackMean a z = a*(z+f*e)/(1+f*z*e) :=
  critical_step_kernel

example : ∀ a : ℝ, 0 < a → a < 1 → ∀ k : ℤ, k ≠ 0 →
    a ≤ |Real.tanh ((k:ℝ)*Real.artanh a)| := posterior_lattice_gap

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 0 ≤ B → B ≤ 4 →
    ENNReal.ofReal (1/6:ℝ) ≤ minimaxRisk μ B := @four_budget_minimax_lower

example : minimaxRisk (Measure.dirac endpointGap) 4 = ENNReal.ofReal (1/6:ℝ) :=
  endpoint_minimax_eq

example : ∀ {n : ℕ} (pol : List Bool → Option ℕ) (s t P : ℝ), 0 < s → s < 1 →
    |t| < 1 → P ≤ 1 → admissibleExitPrice s |t| P →
    let Q := fun (y : ℝ) (w : Prefix n) => creationLaw pol (fun _=>s/2) (fun _=>(1+y)/2) w
    P*(∑ w, (deriv (fun y => Q y w) t)^2/Q t w) ≤ s^2*∑ w, Q t w*workOf w :=
  @adaptive_fisher_price

example : ∀ (s : ℝ), 39/40 ≤ s → s < 1 →
    IntervalIntegrable (nearPerfectEnvelope s) volume 0 1 ∧
    (∫ t in (0:ℝ)..1, nearPerfectEnvelope s t) ≤ 2/3 := near_perfect_integral

example : ∀ (g : Gap) (B : ℝ), 2*g.val < 1 → (2*g.val)^2*B=4 →
    ∀ (K : ℝ → ℝ), Measurable K → IntervalIntegrable K volume (-1) 1 →
    (∃ C : ℝ, ∀ t ∈ Set.Icc (-1:ℝ) 1, 0 ≤ K t ∧ K t ≤ C) →
    (∫ t in (-1:ℝ)..1, K t) ≤ 4/3 →
    (∀ t, |t| < 1 → ∃ P, 0 < P ∧ P ≤ 1 ∧ admissibleExitPrice (2*g.val) |t| P ∧
      (1-t^2)^2 ≤ K t*P) → ENNReal.ofReal (1/6:ℝ) ≤ minimaxRisk (Measure.dirac g) B :=
  minimax_from_tapered_price

example : ∀ (g : Gap) (B : ℝ), 39/40 ≤ 2*g.val → 2*g.val < 1 → (2*g.val)^2*B = 4 →
    ENNReal.ofReal (1/6:ℝ) ≤ minimaxRisk (Measure.dirac g) B := near_perfect_minimax_lower

example : gridChain 16384 endpoints := checked_window

example : ∀ s : ℝ, 2/5 ≤ s → s ≤ 39/40 →
    ∃ hi : ℕ, s ≤ (hi:ℝ)/40960 ∧
      (((hi:ℝ)/40960)/s)^2 * ((upperSum hi:ℝ)/((bins:ℝ)*(scale:ℝ))) ≤ 2/3 := real_window

example : ∀ (g : Gap) (B : ℝ), 2/5 ≤ 2*g.val → 2*g.val ≤ 39/40 →
    (2*g.val)^2*B=4 → ENNReal.ofReal (1/6:ℝ) ≤ minimaxRisk (Measure.dirac g) B := middle_minimax_lower

example : ∀ (g : Gap) (B : ℝ), (2*g.val)^2*B=4 →
    ENNReal.ofReal (1/6:ℝ) ≤ minimaxRisk (Measure.dirac g) B := critical_minimax_lower

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/6) ≤ minimaxRisk μ B := @unrestricted_minimax_lower

example : ∀ c : ℝ, (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*c) ≤ minimaxRisk μ B) ↔ c ≤ 1/6 := universal_coefficient_iff

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25 ≤ B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*Real.sqrt (59/2100:ℝ)) ≤ minimaxRisk μ B :=
  @large_budget_minimax_lower

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (g : Gap) (B : ℝ),
    ENNReal.ofReal (modulus μ g.val)*minimaxRisk (Measure.dirac g) B ≤ minimaxRisk μ B := @critical_gap_reduction

example : ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (g : Gap) (A : AdaptiveEstimator R) (q : SignLaw),
    expectedWork (Measure.dirac g) (sourceEstimator μ g A) q = expectedWork μ A (sourceTarget g q) :=
  @simulation_expected_work

example : ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (g : Gap) (A : AdaptiveEstimator R) (q : SignLaw),
    ENNReal.ofReal (modulus μ g.val) * rootMeanRisk (experimentLaw (Measure.dirac g) (sourceEstimator μ g A) q)
      (populationOutput (sourceEstimator μ g A)) (signMean (Measure.dirac g) q.val) =
    rootMeanRisk (experimentLaw μ A (sourceTarget g q)) (populationOutput A) (signMean μ (sourceTarget g q).val) :=
  @simulation_rms

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/6) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/6) ≤ selectedMinimaxRisk μ B := @oracle_minimax_lower

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25 ≤ B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*Real.sqrt (59/2100:ℝ)) ≤ revealedMinimaxRisk μ B ∧
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*Real.sqrt (59/2100:ℝ)) ≤ selectedMinimaxRisk μ B := @oracle_large_budget_lower

example : revealedMinimaxRisk (Measure.dirac endpointGap) 4 = ENNReal.ofReal (1/6:ℝ) ∧
    selectedMinimaxRisk (Measure.dirac endpointGap) 4 = ENNReal.ofReal (1/6:ℝ) := oracle_endpoint_eq

example : ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (g : Gap) (A : OracleEstimator R) (B : ℝ), OracleBudget A B →
    ENNReal.ofReal (modulus μ g.val)*minimaxRisk (Measure.dirac g) B ≤ oracleRisk μ A := @oracle_gap_reduction
"""


def public_names(source: str, label: str) -> list[str]:
    """Full names of the module's public declarations.

    Each module opens one namespace and declares everything inside it. A
    public declaration must have a name the registry can read; an anonymous
    instance, for example, would be neither registered nor reported.
    """
    namespaces = NAMESPACE.findall(source)
    if len(namespaces) != 1:
        raise ValueError(f"{label} must open exactly one namespace")
    start = NAMESPACE.search(source).start()
    names = []
    for match in ANY_DECLARATION.finditer(source):
        if match.start() < start:
            raise ValueError(f"Declaration before the namespace in {label}")
        if PRIVATE.search(match.group()):
            continue
        name = DECLARATION.match(source, match.start())
        if name is None:
            line = source[match.start():source.find("\n", match.end())].strip()
            raise ValueError("Declaration the registry cannot read: " + line)
        names.append(f"{namespaces[0]}.{name.group(1)}")
    return names


def declared_roots() -> set[str]:
    if {p.stem for p in SOURCES.glob("*.lean")} != set(MODULES) or len(MODULES) != len(set(MODULES)):
        raise ValueError("Unregistered or missing sharp RMS module")
    roots: list[str] = []
    for name in MODULES:
        source = strip_comments((SOURCES / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in SharpRMS/{name}.lean")
        roots.extend(public_names(source, f"SharpRMS/{name}.lean"))
    if len(roots) != len(set(roots)):
        raise ValueError("Duplicate sharp RMS declaration")
    required = {name for pair in TARGETS.items() for name in pair} | set(COMPONENTS)
    found = {root.rsplit(".", 1)[1] for root in roots}
    if required - found:
        raise ValueError("Missing sharp RMS target: " + ", ".join(sorted(required - found)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SOURCES / "Specification.lean") != SPEC_HASH:
        raise ValueError("Changed sharp RMS statement")
    roots = declared_roots()
    source = "\n".join([
        *[f"import {PREFIX}{name}" for name in MODULES],
        "open MeasureTheory InformationTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6",
        "open ThresholdHC.OracleLower ThresholdHC.SharpRMS ThresholdHC.SharpRMS.Window",
        *[f"example : {statement} := {theorem}" for theorem, statement in sorted(TARGETS.items())],
        EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    if source.count("\nexample") != EXACT_COUNT + len(TARGETS):
        raise ValueError("Each target and component needs exactly one restated statement")
    # A count alone accepts one statement restated twice and another not at all.
    for name in list(TARGETS) + list(COMPONENTS):
        if len(re.findall(rf":=\s*@?{re.escape(name)}\n", EXACT)) != 1:
            raise ValueError("Each target and component needs exactly one restated statement")
    return source, roots


def replay_modules() -> list[str]:
    return [PREFIX + name for name in MODULES]


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
        print(f"Replayed {len(MODULES)} modules through the independent kernel checker")
    print("All eight sharp RMS target statements are certified")


if __name__ == "__main__":
    main()
