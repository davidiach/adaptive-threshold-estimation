"""Audit the literal forms of the robust-continuation planner (issue 82).

Subsubsection Robust use of the known-law estimator of the v6 arbitrary-law
adaptation appendix and the deliverables of issue 82: the robust planner's
plan branch as a named estimator, in a tight two-branch form for a coupled and
for every CDF-dominated true law, with the zero-atom quantile split named so
that the statement uses only the reference law, the rarity and the budget;
the large-atom case; the sign allocation induced on the reference law by a
coupling, with its integral identity and the sharp admissibility clause; and
the pathwise correct-time bounds of the race, display (UA15), in parameter
form, at the gap coupling, at the reference zero atom and for the reference
level race. The integrated work bounds of (A15) are not restated.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the eleven targets and three components with their types written out;
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

GROUP = "RobustContinuationForms"
NAMES = ("Specification", "NamedPlanner", "InducedSign", "CorrectTimes", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "4805d9621b012c00c0091b73cc49812e1ef59615a2f9540b2eaa608fe434c5ab"
TARGETS = {
    "RobustContinuationForms.robust_tight_planner_output": "RobustContinuationForms.RobustTightPlannerOutputStatement",
    "RobustContinuationForms.cdf_robust_tight_planner_output": "RobustContinuationForms.CDFRobustTightPlannerOutputStatement",
    "RobustContinuationForms.robust_exact_planner_output": "RobustContinuationForms.RobustExactPlannerOutputStatement",
    "RobustContinuationForms.robust_large_atom_output": "RobustContinuationForms.RobustLargeAtomOutputStatement",
    "RobustContinuationForms.induced_sign_allocation": "RobustContinuationForms.InducedSignAllocationStatement",
    "RobustContinuationForms.correct_time_race_bound": "RobustContinuationForms.CorrectTimeRaceBoundStatement",
    "RobustContinuationForms.correct_time_antitone": "RobustContinuationForms.CorrectTimeAntitoneStatement",
    "RobustContinuationForms.coupled_correct_time_work": "RobustContinuationForms.CoupledCorrectTimeWorkStatement",
    "RobustContinuationForms.coupled_gap_correct_time_work": "RobustContinuationForms.CoupledGapCorrectTimeWorkStatement",
    "RobustContinuationForms.coupled_zero_atom_correct_time_work": "RobustContinuationForms.CoupledZeroAtomCorrectTimeWorkStatement",
    "RobustContinuationForms.reference_race_correct_time_work": "RobustContinuationForms.ReferenceRaceCorrectTimeWorkStatement",
}
COMPONENTS = (
    "RobustContinuationForms.inducedSignMeasure_le_marginal",
    "RobustContinuationForms.signOrdered_uniformCoinTape",
    "RobustContinuationForms.gapParameter_signOrder",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {z₀ ρ B : ℝ} {N : ℕ}
    (hz0 : 0 ≤ z₀) (hzρ : z₀ < ρ) (hρ4 : ρ ≤ 1/4), 0 < B →
    ∀ (hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀)),
    τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀) →
    (∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) → (∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) →
    ∀ (hN : bandEdge N < quantileThreshold η (conditionalRarity ρ z₀))
      (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (z₀ + ζ.real univ))
      (w : Fin (planTerminal (hz0.trans_lt hzρ) B E.unresolved + 1) → ℝ),
    (∀ i, Real.sqrt (17*levelAccuracy ρ i.val / planCost E ρ
        (searchCaps E.resolvedError hE.vanishes (hz0.trans_lt hzρ))
        (planTerminal (hz0.trans_lt hzρ) B E.unresolved) i) ≤ w i) →
    (∀ i, w i ≤ 2 * Real.sqrt (17*levelAccuracy ρ i.val / planCost E ρ
        (searchCaps E.resolvedError hE.vanishes (hz0.trans_lt hzρ))
        (planTerminal (hz0.trans_lt hzρ) B E.unresolved) i)) →
    (RunsPlan E (hz0.trans_lt hzρ) hE.vanishes B w →
      ∀ (π : Measure (Gap × Gap)) (μ₀ μ : Measure Gap) [IsFiniteMeasure π]
        [IsFiniteMeasure μ₀] [IsProbabilityMeasure μ],
        (∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) → π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η →
        μ = π.map Prod.snd + μ₀ →
        RareBudget μ (robustQuantilePlanEstimator η σ τ ζ hz0 hzρ hρ4 hcore hN E hE.vanishes B w)
            ρ B ∧
          rareRisk μ (robustQuantilePlanEstimator η σ τ ζ hz0 hzρ hρ4 hcore hN E hE.vanishes B w)
              ρ ≤
            ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B) ∧
    (¬ RunsPlan E (hz0.trans_lt hzρ) hE.vanishes B w →
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        RareBudget μ (constantEstimator (ρ/2)) ρ B ∧
          rareRisk μ (constantEstimator (ρ/2)) ρ ≤
            ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B) :=
  RobustContinuationForms.robust_tight_planner_output

example :
  ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {z₀ ρ B : ℝ} {N : ℕ}
    (hz0 : 0 ≤ z₀) (hzρ : z₀ < ρ) (hρ4 : ρ ≤ 1/4), 0 < B →
    ∀ (hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀)),
    τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀) →
    (∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) → (∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) →
    ∀ (hN : bandEdge N < quantileThreshold η (conditionalRarity ρ z₀))
      (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (z₀ + ζ.real univ))
      (w : Fin (planTerminal (hz0.trans_lt hzρ) B E.unresolved + 1) → ℝ),
    (∀ i, Real.sqrt (17*levelAccuracy ρ i.val / planCost E ρ
        (searchCaps E.resolvedError hE.vanishes (hz0.trans_lt hzρ))
        (planTerminal (hz0.trans_lt hzρ) B E.unresolved) i) ≤ w i) →
    (∀ i, w i ≤ 2 * Real.sqrt (17*levelAccuracy ρ i.val / planCost E ρ
        (searchCaps E.resolvedError hE.vanishes (hz0.trans_lt hzρ))
        (planTerminal (hz0.trans_lt hzρ) B E.unresolved) i)) →
    (RunsPlan E (hz0.trans_lt hzρ) hE.vanishes B w →
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        (∀ x, cdf (μ.map Subtype.val) x ≤ cdf (zeroAtomLaw z₀ η) x) →
        RareBudget μ (robustQuantilePlanEstimator η σ τ ζ hz0 hzρ hρ4 hcore hN E hE.vanishes B w)
            ρ B ∧
          rareRisk μ (robustQuantilePlanEstimator η σ τ ζ hz0 hzρ hρ4 hcore hN E hE.vanishes B w)
              ρ ≤
            ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B) ∧
    (¬ RunsPlan E (hz0.trans_lt hzρ) hE.vanishes B w →
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        RareBudget μ (constantEstimator (ρ/2)) ρ B ∧
          rareRisk μ (constantEstimator (ρ/2)) ρ ≤
            ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B) :=
  RobustContinuationForms.cdf_robust_tight_planner_output

example :
  ∀ (η : Measure Gap) [IsProbabilityMeasure η] {z₀ ρ B : ℝ}
    (hz0 : 0 ≤ z₀) (hzρ : z₀ < ρ) (hρ4 : ρ ≤ 1/4), 0 < B →
    (RobustRunsPlan η B hz0 hzρ hρ4 →
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        (∀ x, cdf (μ.map Subtype.val) x ≤ cdf (zeroAtomLaw z₀ η) x) →
        RareBudget μ (robustPlannerPlan η B hz0 hzρ hρ4) ρ B ∧
          rareRisk μ (robustPlannerPlan η B hz0 hzρ hρ4) ρ ≤
            ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B) ∧
    (¬ RobustRunsPlan η B hz0 hzρ hρ4 →
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        RareBudget μ (constantEstimator (ρ/2)) ρ B ∧
          rareRisk μ (constantEstimator (ρ/2)) ρ ≤
            ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B) :=
  RobustContinuationForms.robust_exact_planner_output

example :
  ∀ (η : Measure Gap) [IsProbabilityMeasure η] {z₀ ρ B : ℝ}, 0 < ρ → 0 < B → ρ ≤ z₀ →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      RareBudget μ (constantEstimator (ρ/2)) ρ B ∧
        rareRisk μ (constantEstimator (ρ/2)) ρ ≤
          ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B :=
  RobustContinuationForms.robust_large_atom_output

example :
  ∀ (η : Measure Gap) [IsProbabilityMeasure η] {z₀ ρ : ℝ}, 0 ≤ z₀ → z₀ < 1 →
  ∀ (π : Measure (Gap × Gap)) (μ₀ μ : Measure Gap) [IsFiniteMeasure π]
    [IsFiniteMeasure μ₀] [IsProbabilityMeasure μ],
    π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η → μ = π.map Prod.snd + μ₀ →
    ∀ q : SignLaw,
      (∀ F : Gap → ℝ, Measurable F →
        (∫ z, q.val z.2 * F z.1 ∂π) = (1 - z₀) * ∫ d, (inducedSignLaw π q).val d * F d ∂η) ∧
      (1 - z₀) * signMean η (inducedSignLaw π q).val + (∫ d, q.val d ∂μ₀) = signMean μ q.val ∧
      (RarePrior μ ρ q →
        (1 - z₀) * signMean η (inducedSignLaw π q).val + (∫ d, q.val d ∂μ₀) ≤ ρ ∧
          RarePrior η (ρ / (1 - z₀)) (inducedSignLaw π q)) :=
  RobustContinuationForms.induced_sign_allocation

example :
  ∀ (neg pos : PrefixTest) (L : ℕ) (s : Bool) (ω : ℕ → Bool),
    (raceCost neg pos L ω : ℕ∞) ≤
      2 * min (bankCorrectTime neg pos s ω) (ordinaryCorrectTime s L (parityTape 1 ω) : ℕ∞) :=
  RobustContinuationForms.correct_time_race_bound

example :
  ∀ (neg pos : PrefixTest), DownwardTest neg → UpwardTest pos →
  ∀ (L : ℕ) (s : Bool) (ω₀ ω₁ : ℕ → Bool), SignOrdered s ω₀ ω₁ →
    bankCorrectTime neg pos s ω₁ ≤ bankCorrectTime neg pos s ω₀ ∧
      ordinaryCorrectTime s L (parityTape 1 ω₁) ≤ ordinaryCorrectTime s L (parityTape 1 ω₀) :=
  RobustContinuationForms.correct_time_antitone

example :
  ∀ (neg pos : PrefixTest), DownwardTest neg → UpwardTest pos →
  ∀ (L : ℕ) (s : Bool) (p₀ p : unitInterval), cond s ((p₀:ℝ) ≤ p) ((p:ℝ) ≤ p₀) →
  ∀ u : ℕ → ℝ,
    (raceCost neg pos L (CriticalEntropy.uniformCoinTape p u) : ℕ∞) ≤
      2 * min (bankCorrectTime neg pos s (CriticalEntropy.uniformCoinTape p u))
        (ordinaryCorrectTime s L (parityTape 1 (CriticalEntropy.uniformCoinTape p u)) : ℕ∞) ∧
    2 * min (bankCorrectTime neg pos s (CriticalEntropy.uniformCoinTape p u))
        (ordinaryCorrectTime s L (parityTape 1 (CriticalEntropy.uniformCoinTape p u)) : ℕ∞) ≤
      2 * min (bankCorrectTime neg pos s (CriticalEntropy.uniformCoinTape p₀ u))
        (ordinaryCorrectTime s L (parityTape 1 (CriticalEntropy.uniformCoinTape p₀ u)) : ℕ∞) :=
  RobustContinuationForms.coupled_correct_time_work

example :
  ∀ (neg pos : PrefixTest), DownwardTest neg → UpwardTest pos →
  ∀ (L : ℕ) (s : Bool) (d₀ d : Gap), (d₀:ℝ) ≤ d → ∀ u : ℕ → ℝ,
    (raceCost neg pos L
        (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u) : ℕ∞) ≤
      2 * min (bankCorrectTime neg pos s
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u))
        (ordinaryCorrectTime s L (parityTape 1
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u)) : ℕ∞) ∧
    2 * min (bankCorrectTime neg pos s
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u))
        (ordinaryCorrectTime s L (parityTape 1
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u)) : ℕ∞) ≤
      2 * min (bankCorrectTime neg pos s
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d₀) u))
        (ordinaryCorrectTime s L (parityTape 1
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d₀) u)) : ℕ∞) :=
  RobustContinuationForms.coupled_gap_correct_time_work

example :
  ∀ (neg pos : PrefixTest), DownwardTest neg → UpwardTest pos →
  ∀ (L : ℕ) (s : Bool) (d : Gap) (p₀ : unitInterval), (p₀:ℝ) = 1/2 → ∀ u : ℕ → ℝ,
    (raceCost neg pos L
        (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u) : ℕ∞) ≤
      2 * min (bankCorrectTime neg pos s
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u))
        (ordinaryCorrectTime s L (parityTape 1
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u)) : ℕ∞) ∧
    2 * min (bankCorrectTime neg pos s
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u))
        (ordinaryCorrectTime s L (parityTape 1
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u)) : ℕ∞) ≤
      2 * min (bankCorrectTime neg pos s (CriticalEntropy.uniformCoinTape p₀ u))
        (ordinaryCorrectTime s L (parityTape 1 (CriticalEntropy.uniformCoinTape p₀ u)) : ℕ∞) :=
  RobustContinuationForms.coupled_zero_atom_correct_time_work

example :
  ∀ (η : Measure Gap) [IsProbabilityMeasure η] (w : ℕ → ℝ≥0) (hw : HasSum w 1) {c : ℝ}
    (hc : 0 < c) {ρ : ℝ} (hρc : ρ ≤ c) (κ : ℕ → ℕ) (l : ℕ) (s : Bool) (p₀ p : unitInterval),
    cond s ((p₀:ℝ) ≤ p) ((p:ℝ) ≤ p₀) → ∀ u : ℕ → ℝ,
    ((robustFamily η w hw hc hρc κ l).cost (CriticalEntropy.uniformCoinTape p u) : ℕ∞) ≤
      2 * min (bankCorrectTime (negativeBankTest w (levelEpsilon l))
          (positiveBankTest η w (ρ*levelEpsilon l/c)) s (CriticalEntropy.uniformCoinTape p u))
        (ordinaryCorrectTime s (2 * κ l)
          (parityTape 1 (CriticalEntropy.uniformCoinTape p u)) : ℕ∞) ∧
    2 * min (bankCorrectTime (negativeBankTest w (levelEpsilon l))
          (positiveBankTest η w (ρ*levelEpsilon l/c)) s (CriticalEntropy.uniformCoinTape p u))
        (ordinaryCorrectTime s (2 * κ l)
          (parityTape 1 (CriticalEntropy.uniformCoinTape p u)) : ℕ∞) ≤
      2 * min (bankCorrectTime (negativeBankTest w (levelEpsilon l))
          (positiveBankTest η w (ρ*levelEpsilon l/c)) s (CriticalEntropy.uniformCoinTape p₀ u))
        (ordinaryCorrectTime s (2 * κ l)
          (parityTape 1 (CriticalEntropy.uniformCoinTape p₀ u)) : ℕ∞) :=
  RobustContinuationForms.reference_race_correct_time_work

example : ∀ (π : Measure (Gap × Gap)) (q : SignLaw),
    inducedSignMeasure π q ≤ π.map Prod.fst :=
  RobustContinuationForms.inducedSignMeasure_le_marginal

example : ∀ (s : Bool) {p₀ p : unitInterval},
    cond s ((p₀:ℝ) ≤ p) ((p:ℝ) ≤ p₀) → ∀ (u : ℕ → ℝ),
    SignOrdered s (CriticalEntropy.uniformCoinTape p₀ u) (CriticalEntropy.uniformCoinTape p u) :=
  @RobustContinuationForms.signOrdered_uniformCoinTape

example : ∀ (s : Bool) {d₀ d : Gap}, (d₀:ℝ) ≤ d →
    cond s (((ObservableSimulation.gapParameter s d₀ : unitInterval) : ℝ) ≤
        (ObservableSimulation.gapParameter s d : unitInterval))
      (((ObservableSimulation.gapParameter s d : unitInterval) : ℝ) ≤
        (ObservableSimulation.gapParameter s d₀ : unitInterval)) :=
  @RobustContinuationForms.gapParameter_signOrder
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
        raise ValueError("Duplicate robust-continuation-forms declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing robust-continuation-forms target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed robust-continuation-forms specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open Set NNReal ThresholdHC open ThresholdHC.Tier6 (Gap SignLaw AdaptiveEstimator signMean) open ThresholdHC.EntropyTailUpper ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailAssembly ThresholdHC.EntropyTailExecution ThresholdHC.KnownLawPlanner ThresholdHC.ArbitraryLawAdaptation ThresholdHC.RobustContinuation ThresholdHC.RobustContinuationForms",
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
    print(f"All {len(TARGETS)} robust-continuation-forms targets are certified")


if __name__ == "__main__":
    main()
