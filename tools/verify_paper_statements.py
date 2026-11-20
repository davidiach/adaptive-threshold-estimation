"""Audit paper and guide claims that had only a written proof, numerics or an existential constant.

* The critical law: the density 32d on (0,1/4] is the exact power law
  F(d) = (4d)^2, the critical theorem's minimax risk is the rare-event minimax
  risk of that law, and so the critical theorem holds with the explicit lower
  constant 10^-18 (the upper constant 100000 is the existing one). The
  arithmetic of the slow-divergence remark, sqrt H < 2.54 for
  rho >= 10^-100, and the paper's Psi sequence rho_n = exp(-exp n),
  B_n = rho_n^-2, restated in the critical theorem's own model (it was
  already checked in the rare-event experiment).
* The unbiased coefficient: at a fixed gap d some estimator is unbiased with
  expected work at most one and largest variance 1/(16 d^2) (the proof uses one
  fresh observation), so inf VW = I^2/16 and 1/16 is the largest valid
  universal coefficient. At the gap 1/2 some such estimator is [0,1]-valued.
  For B >= 1 a known point mass has minimax RMS risk at most half its modulus
  at B^-1/2 (from a research note).
* The observable 713 construction has sup_q E Y^2 <= 23 I and work 31 I.
* The sharp quantile factor exceeds 1.462554551279, the lower end of the
  paper's decimal bracket, so some finite law has Q > 1.462554551279 K, and
  selection stability holds with the lower endpoints 20Q/31 and Q/c_vec.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the fifteen targets and five component theorems with their types
   written out, so a changed statement cannot pass under an old name;
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

GROUP = "PaperStatements"
NAMES = ("Specification", "Critical", "OneFlip", "Observable", "Quantile", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "bc1365f23fec761d2e212185074d78adc5c9896c801a3cefb4d5c88e3d7d3a9a"
TARGETS = {
    "PaperStatements.critical_power_law_exact": "PaperStatements.CriticalPowerLawStatement",
    "PaperStatements.critical_model": "PaperStatements.CriticalModelStatement",
    "PaperStatements.critical_explicit_constants": "PaperStatements.CriticalExplicitStatement",
    "PaperStatements.critical_slow_divergence": "PaperStatements.SlowDivergenceStatement",
    "PaperStatements.critical_psi_divergence": "PaperStatements.CriticalPsiSequenceStatement",
    "PaperStatements.one_flip": "PaperStatements.OneFlipStatement",
    "PaperStatements.unbiased_fixed_gap_equality": "PaperStatements.FixedGapEqualityStatement",
    "PaperStatements.unbiased_sharp_coefficient": "PaperStatements.UnbiasedSharpStatement",
    "PaperStatements.half_gap_one_flip": "PaperStatements.HalfGapUnbiasedStatement",
    "PaperStatements.point_mass_half": "PaperStatements.PointMassUpperStatement",
    "PaperStatements.observable_second_moment": "PaperStatements.SecondMomentStatement",
    "PaperStatements.quantile_root_lower": "PaperStatements.RootLowerStatement",
    "PaperStatements.quantile_finite_ratio": "PaperStatements.FiniteRatioStatement",
    "PaperStatements.selection_stability_quantile": "PaperStatements.StabilityQuantileStatement",
    "PaperStatements.selection_stability_sharp": "PaperStatements.StabilitySharpStatement",
}
COMPONENTS = (
    "PaperStatements.log_ten_lt",
    "PaperStatements.binomial_square",
    "PaperStatements.variance_work_lower",
    "PaperStatements.output_second_moment_le",
    "PaperStatements.root_series_lower",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example : ExactPowerLaw ConfidenceTransfer.criticalPositiveLaw 2 (1/4) :=
  PaperStatements.critical_power_law_exact

example : ∀ ρ B : ℝ, CriticalEntropy.criticalMinimaxRisk ρ B =
    rareMinimaxRisk ConfidenceTransfer.criticalPositiveLaw ρ B :=
  PaperStatements.critical_model

example : ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    let C := Real.sqrt (ρ * CriticalEntropy.criticalLogFactor ρ / B)
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 18 * min ρ C) ≤ CriticalEntropy.criticalMinimaxRisk ρ B ∧
      CriticalEntropy.criticalMinimaxRisk ρ B ≤ ENNReal.ofReal (100000 * min ρ C) :=
  PaperStatements.critical_explicit_constants

example : ∀ ρ : ℝ, (10 : ℝ)⁻¹ ^ 100 ≤ ρ → ρ ≤ 1/4 →
    Real.sqrt (1 + Real.log (1 + Real.log (1/ρ))) < 127/50 :=
  PaperStatements.critical_slow_divergence

example : ∀ n : ℕ, 3 ≤ n →
    let ρ := Real.exp (-Real.exp n)
    let B := 1 / ρ ^ 2
    0 < CriticalPsi.criticalPsi ρ (1 / Real.sqrt B) ∧
    ENNReal.ofReal ((10 : ℝ)⁻¹ ^ 18 / 16 * Real.sqrt (1 + Real.log (1 + Real.log (1/ρ))) *
        CriticalPsi.criticalPsi ρ (1 / Real.sqrt B)) ≤ CriticalEntropy.criticalMinimaxRisk ρ B ∧
    Real.sqrt (1 + n) ≤ Real.sqrt (1 + Real.log (1 + Real.log (1/ρ))) :=
  PaperStatements.critical_psi_divergence

example : ∀ d : Gap, ∃ A : AdaptiveEstimator Unit,
    UniformlyUnbiased (Measure.dirac d) A ∧
    UniformVarianceBound (Measure.dirac d) A (1 / (16 * (d : ℝ)^2)) ∧
    UniformBudget (Measure.dirac d) A 1 ∧
    (⨆ q : SignLaw, evariance (populationOutput A) (experimentLaw (Measure.dirac d) A q)) =
      ENNReal.ofReal (1 / (16 * (d : ℝ)^2)) :=
  PaperStatements.one_flip

example : ∀ d : Gap, PaperStatements.unbiasedVarianceWork (Measure.dirac d) =
    ENNReal.ofReal ((∫ x : Gap, (x : ℝ)⁻¹ ∂Measure.dirac d)^2 / 16) :=
  PaperStatements.unbiased_fixed_gap_equality

example : ∀ c : ℝ,
    (∀ (μ : Measure Gap) [IsProbabilityMeasure μ], Integrable (fun d : Gap => (d : ℝ)⁻¹) μ →
      ENNReal.ofReal (c * (∫ d : Gap, (d : ℝ)⁻¹ ∂μ)^2) ≤ PaperStatements.unbiasedVarianceWork μ) ↔
    c ≤ 1/16 :=
  PaperStatements.unbiased_sharp_coefficient

example : ∃ A : AdaptiveEstimator Unit,
    (∀ z, 0 ≤ populationOutput A z ∧ populationOutput A z ≤ 1) ∧
    UniformlyUnbiased (Measure.dirac (⟨1/2, by norm_num⟩ : Gap)) A ∧
    UniformBudget (Measure.dirac (⟨1/2, by norm_num⟩ : Gap)) A 1 :=
  PaperStatements.half_gap_one_flip

example : ∀ (g : Gap) (B : ℝ), 1 ≤ B →
    minimaxRisk (Measure.dirac g) B ≤
      ENNReal.ofReal (modulus (Measure.dirac g) (1 / Real.sqrt B) / 2) :=
  PaperStatements.point_mass_half

example : ∃ A : AdaptiveEstimator ℕ,
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      Integrable (fun d : Gap => (d : ℝ)⁻¹) μ →
      UniformlyUnbiased μ A ∧
      (∀ q : SignLaw, (∫⁻ z, ENNReal.ofReal ((populationOutput A z)^2) ∂experimentLaw μ A q) ≤
        ENNReal.ofReal (23 * ∫ d : Gap, (d : ℝ)⁻¹ ∂μ)) ∧
      UniformBudget μ A (31 * ∫ d : Gap, (d : ℝ)⁻¹ ∂μ) :=
  PaperStatements.observable_second_moment

example : (1462554551279/1000000000000 : ℝ) < OptimalQuantile.scalarRoot :=
  PaperStatements.quantile_root_lower

example : ∃ (μ : Measure Gap) (_ : IsProbabilityMeasure μ), μ.support.Finite ∧
    ∃ ρ B : ℝ, 0 < ρ ∧ ρ ≤ 1/4 ∧ 0 < B ∧
      ENNReal.ofReal (1462554551279/1000000000000) * EntropyTail.selection μ ρ B <
        EntropyTailQuantile.closedQuantileValue μ ρ B :=
  PaperStatements.quantile_finite_ratio

example : ∀ (μ μ₀ : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ₀]
    (T : Gap → Gap), Measurable T → ∀ {r η ρ B : ℝ}, 1 ≤ r → 0 < ρ → ρ ≤ 1/4 → 0 < B →
    tvDist μ μ₀ / 2 ≤ η →
    (∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ)) →
    (∀ j, T ⁻¹' EntropyTail.band j = EntropyTail.band j) →
    let Q := (EntropyTailQuantile.closedQuantileValue (μ₀.map T) ρ B).toReal
    max 0 (20/31*Q - η) ≤ (EntropyTail.selection μ ρ B).toReal ∧
      (EntropyTail.selection μ ρ B).toReal ≤ min ρ (r*Q + η) :=
  PaperStatements.selection_stability_quantile

example : ∀ (μ μ₀ : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ₀]
    (T : Gap → Gap), Measurable T → ∀ {r η ρ B : ℝ}, 1 ≤ r → 0 < ρ → ρ ≤ 1/4 → 0 < B →
    tvDist μ μ₀ / 2 ≤ η →
    (∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ)) →
    (∀ j, T ⁻¹' EntropyTail.band j = EntropyTail.band j) →
    let Q := (EntropyTailQuantile.closedQuantileValue (μ₀.map T) ρ B).toReal
    max 0 (Q / OptimalQuantile.scalarRoot - η) ≤ (EntropyTail.selection μ ρ B).toReal ∧
      (EntropyTail.selection μ ρ B).toReal ≤ min ρ (r*Q + η) :=
  PaperStatements.selection_stability_sharp

example : Real.log 10 < 230304/100000 :=
  PaperStatements.log_ten_lt

example : ∀ (b a c : ℝ) (n k : ℕ),
    SharpRMS.LargeBudget.binomialAverage b (fun j => (a * j + c)^2) n k =
      (a * (k + n * b) + c)^2 + a^2 * n * b * (1 - b) :=
  PaperStatements.binomial_square

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    ENNReal.ofReal ((∫ d : Gap, (d:ℝ)⁻¹ ∂μ)^2 / 16) ≤ PaperStatements.unbiasedVarianceWork μ :=
  PaperStatements.variance_work_lower

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    Integrable (fun d : Gap => (d : ℝ)⁻¹) μ →
    (∫⁻ z, ENNReal.ofReal ((populationOutput Observable713.observableEstimator z)^2)
        ∂experimentLaw μ Observable713.observableEstimator q) ≤
      ENNReal.ofReal (23 * ∫ d : Gap, (d : ℝ)⁻¹ ∂μ) :=
  PaperStatements.output_second_moment_le

example : 1 < OptimalQuantile.partitionSeries (1462554551279/1000000000000) (12591049/10000000) :=
  PaperStatements.root_series_lower
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
        raise ValueError("Duplicate paper-statement declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing paper-statement target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed paper-statement specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.UnbiasedConverse",
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
    print(f"All {len(TARGETS)} paper-statement targets are certified")


if __name__ == "__main__":
    main()
