"""Audit the smooth-density construction and original-experiment information bound."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.SmoothDensity.Separation
import ThresholdHC.SmoothDensity.Information
import ThresholdHC.SmoothDensity.Scale
noncomputable section
open MeasureTheory InformationTheory ThresholdHC.SmoothDensity
open ThresholdHC.Tier6 ThresholdHC.Confidence
open scoped ENNReal ContDiff

example (k : ℕ) (x : ℝ) : |iteratedDeriv k profile x| ≤ k.factorial :=
  profile_derivative_bound k x

example {s k : ℕ} (hk : k ≤ s) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (x : ℝ) :
    |iteratedDeriv k (perturbation s t) x| ≤ k.factorial / 8 :=
  perturbation_derivative_bound hk ht ht1 x

example (s : ℕ) (t a : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (ha : |a| ≤ 2) :
    ContDiff ℝ ∞ (density s t a) ∧
    (∀ p, 0 ≤ density s t a p) ∧
    (∀ p, p ∉ Set.Icc (1 / 4 : ℝ) (3 / 4) → density s t a p = 0) ∧
    (∫ p, density s t a p) = 1 :=
  ⟨density_contDiff s t a,fun p => centeredDensity_nonneg s ht ht1 ha (p - 1 / 2),
    density_supported s t a,density_integral s t a⟩

example (s : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (t a : ℝ), 0 < t → t ≤ 1 → |a| ≤ 2 →
      ∀ k ≤ s, ∀ p, |iteratedDeriv k (density s t a) p| ≤ M :=
  exists_uniform_density_bound s

example (s : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 64) :
    t ^ (s + 1) / 8 * Real.log (1 / t) ≤
      (∫ x in Set.Ioi (0 : ℝ), centeredDensity s t 2 x) -
        ∫ x in Set.Ioi (0 : ℝ), centeredDensity s t (-2) x :=
  centered_pair_separation s ht ht1

example {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (η : Gap → ℝ) (hη : Measurable η)
    (hηb : ∀ d, 0 ≤ η d ∧ η d ≤ 1 / 8)
    (qp qm : SignLaw) (hp : ∀ d, qp.val d = 1 / 2 + η d)
    (hm : ∀ d, qm.val d = 1 / 2 - η d)
    (B h : ℝ) (hh : 0 < h) (hgap : ∀ d : Gap, (d : ℝ) * η d ≤ h / 8)
    (hwork : expectedWork μ A qp ≤ ENNReal.ofReal B) :
    klDiv (experimentLaw μ A qp) (experimentLaw μ A qm) ≤
      ENNReal.ofReal ((128 / 225 : ℝ) * h ^ 2 * B) :=
  hidden_local_pair_information μ A η hη hηb qp qm hp hm B h hh hgap hwork

example (s : ℕ) {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ radiusCutoff s) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 64 ∧
      t ^ (s + 1) = scaleConstant s * ε / Real.log (1 / ε) ∧
      2 * ε < t ^ (s + 1) / 8 * Real.log (1 / t) :=
  choose_smooth_scale s hε hsmall
""".lstrip()
    roots = {"ThresholdHC.SmoothDensity." + name for name in [
        "profile_contDiff", "profile_iteratedDeriv", "profile_derivative_bound",
        "perturbation_contDiff", "perturbation_rational", "perturbation_odd",
        "perturbation_nonneg", "perturbation_abs_le", "gap_mul_perturbation_le",
        "perturbation_derivative_bound", "baseDensity_contDiff", "baseDensity_compact",
        "baseDensity_nonneg", "baseDensity_integrable", "baseDensity_integral",
        "baseDensity_even", "baseDensity_zero", "baseDensity_core", "baseDerivative_bounded",
        "density_contDiff", "density_supported", "density_integral",
        "exists_uniform_density_bound", "centered_pair_separation",
        "local_pair_information", "hidden_local_pair_information", "local_pair_confidence_cost",
        "radiusCutoff_pos", "choose_smooth_scale",
    ]}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.SmoothDensity.Separation",
                    "ThresholdHC.SmoothDensity.Information", "ThresholdHC.SmoothDensity.Scale"],
                   cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source, text=True,
                         encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
