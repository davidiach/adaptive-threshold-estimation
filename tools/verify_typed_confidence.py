"""Audit adaptive-type population information transfer."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.TypedConfidence.NullTransfer
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.CriticalEntropy
open ThresholdHC.ConfidenceTransfer ThresholdHC.TypedConfidence
local instance : MeasurableSpace (Option Bool) := ⊤
local instance : MeasurableSingletonClass (Option Bool) := ⟨fun _ => trivial⟩

example : ∀ {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (p q : I → ℝ) (hs : ∀ i, q i = 0 → p i = 0),
    let ref := a * ∏ i, p i
    ref * Real.log (ref / (a * ∏ i, q i)) =
      ∑ i, ref * Real.log (ref / (a * ∏ j, if j=i then q j else p j)) :=
  @ThresholdHC.TypedConfidence.factor_leaf_log

example : ∀ {I Z : Type} [Fintype I] [DecidableEq I] [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (a : Z → ℝ) (p q : I → Z → ℝ) (P Q : Z → ℝ) (H : I → Z → ℝ)
    (hP : ∀ z, P z = a z*∏ i, p i z) (hQ : ∀ z, Q z = a z*∏ i, q i z)
    (hH : ∀ i z, H i z = a z*∏ j, if j=i then q j z else p j z)
    (hs : ∀ i z, q i z = 0 → p i z = 0)
    (pn : (∀ z, 0 ≤ P z) ∧ ∑ z, P z = 1) (qn : (∀ z, 0 ≤ Q z) ∧ ∑ z, Q z = 1)
    (hn : ∀ i, (∀ z, 0 ≤ H i z) ∧ ∑ z, H i z = 1),
    klDiv (finiteWeightMeasure P) (finiteWeightMeasure Q) =
      ∑ i, klDiv (finiteWeightMeasure P) (finiteWeightMeasure (H i)) :=
  @ThresholdHC.TypedConfidence.factorized_kl_sum

example : ∀ {m : ℕ}
    (κ : Fin m → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (τ υ : Measure unitInterval) [IsProbabilityMeasure τ] [IsProbabilityMeasure υ]
    (pol : List Bool → Option (Fin m)) (n : ℕ) (i : Fin m),
    (hellingerAffinity (parameterCappedLaw κ τ pol n i) (parameterCappedLaw κ υ pol n i)).toReal ≤
      (hellingerAffinity (parameterWordLaw (Function.update κ i τ) pol n)
        (parameterWordLaw (Function.update κ i υ) pol n)).toReal :=
  @ThresholdHC.TypedConfidence.parameter_local_affinity

example : ∀ {m n : ℕ}
    (κ τ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ i, IsProbabilityMeasure (τ i)]
    (pol : List Bool → Option (Fin m)) (K : ℝ) (hK : 0 ≤ K)
    (hbound : let ref := fun i => quarterMix (κ i) (τ i)
      ∀ i : Fin m,
        1-(hellingerAffinity (parameterCappedLaw ref (κ i) pol n i)
          (parameterCappedLaw ref (τ i) pol n i)).toReal ≤
        K*(parameterLocalWork ref pol n i).toReal),
    let ref := fun i => quarterMix (κ i) (τ i)
    let alt := fun i => quarterMix (τ i) (κ i)
    klDiv (parameterWordLaw ref pol n) (parameterWordLaw alt pol n) ≤
      ENNReal.ofReal ((8/3)*K*(parameterExpectedWork ref pol n).toReal) :=
  @ThresholdHC.TypedConfidence.finite_parameter_reference_kl

example : ∀ {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Fin m → Measure D) [∀ i, IsProbabilityMeasure (μ i)]
    (p₀ p₁ q r : Fin m → D → unitInterval)
    (h₀ : ∀ i, Measurable (p₀ i)) (h₁ : ∀ i, Measurable (p₁ i))
    (hq : ∀ i, Measurable (q i)) (hr : ∀ i, Measurable (r i))
    (hqhalf : ∀ i x, (q i x : ℝ) ≤ 1/2) (hrhalf : ∀ i x, (r i x : ℝ) ≤ 1/2)
    (pol : List Bool → Option (Fin m)) (K : ℝ) (hK : 0 ≤ K)
    (hlocal : ∀ i, LocalNullWorkBound (μ i) (p₀ i) (p₁ i) (q i) (r i) K),
    let ref := fun i => populationParameterLaw (μ i) (p₀ i) (p₁ i) (quarterPrior (q i) (r i))
    let alt := fun i => populationParameterLaw (μ i) (p₀ i) (p₁ i) (quarterPrior (r i) (q i))
    klDiv (parameterWordLaw ref pol n) (parameterWordLaw alt pol n) ≤
      ENNReal.ofReal ((16/3)*K*(parameterExpectedWork ref pol n).toReal) :=
  @ThresholdHC.TypedConfidence.finite_typed_null_work_kl

example : ∀ (κ τ : Measure unitInterval)
    [IsProbabilityMeasure κ] [IsProbabilityMeasure τ],
    parameterTapeLaw (quarterMix κ τ) = quarterMix (parameterTapeLaw κ) (parameterTapeLaw τ) :=
  @ThresholdHC.TypedConfidence.parameterTapeLaw_quarter

example : ∀ {m n : ℕ} (pol : List Bool → Option (Fin m))
    (w : Prefix n) (i : Fin m) (κ τ : Measure unitInterval)
    [IsProbabilityMeasure κ] [IsProbabilityMeasure τ],
    coinMass pol w i (quarterMix κ τ) =
      (3*coinMass pol w i κ + coinMass pol w i τ)/4 :=
  @ThresholdHC.TypedConfidence.coinMass_quarter

example : ∀ {m : ℕ}
    (κ : Fin m → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (τ : Measure unitInterval) [IsProbabilityMeasure τ]
    (n : ℕ) (pol : List Bool → Option (Fin m)) (i : Fin m),
    ((Measure.pi (fun j => parameterTapeLaw (κ j))).prod (parameterTapeLaw τ)).map
      (localSimulationProcedure i n pol).output =
        parameterWordLaw (Function.update κ i τ) pol n :=
  @ThresholdHC.TypedConfidence.parameter_local_word_law

example : ∀ {m : ℕ}
    (κ : Fin m → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (τ υ : Measure unitInterval) [IsProbabilityMeasure τ] [IsProbabilityMeasure υ]
    (n : ℕ) (pol : List Bool → Option (Fin m)) (i : Fin m),
    parameterWordLaw (Function.update κ i (quarterMix τ υ)) pol n =
      quarterMix (parameterWordLaw (Function.update κ i τ) pol n)
        (parameterWordLaw (Function.update κ i υ) pol n) :=
  @ThresholdHC.TypedConfidence.parameter_one_slot_quarter

example : ∀ {m n : ℕ}
    (κ τ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ i, IsProbabilityMeasure (τ i)]
    (pol : List Bool → Option (Fin m))
    (hs : ∀ i (w : Prefix n), coinMass pol w i (τ i) = 0 → coinMass pol w i (κ i) = 0),
    klDiv (parameterWordLaw κ pol n) (parameterWordLaw τ pol n) =
      ∑ i : Fin m, klDiv (parameterWordLaw κ pol n)
        (parameterWordLaw (Function.update κ i (τ i)) pol n) :=
  @ThresholdHC.TypedConfidence.parameter_hybrid_kl

example : ∀ {m n : ℕ}
    (κ τ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ i, IsProbabilityMeasure (τ i)]
    (pol : List Bool → Option (Fin m)),
    let ref := fun i => quarterMix (κ i) (τ i)
    let alt := fun i => quarterMix (τ i) (κ i)
    klDiv (parameterWordLaw ref pol n) (parameterWordLaw alt pol n) =
      ∑ i : Fin m, klDiv (parameterWordLaw ref pol n)
        (parameterWordLaw (Function.update ref i (alt i)) pol n) :=
  @ThresholdHC.TypedConfidence.quarter_parameter_hybrid_kl

example : ∀ {m : ℕ} (κ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] (pol : List Bool → Option (Fin m)) (n : ℕ),
    (Measure.pi (fun i => parameterTapeLaw (κ i))).map
      (fun raw => (populationSimulation pol n raw).2) = parameterWordLaw κ pol n :=
  @ThresholdHC.TypedConfidence.parameter_word_law

example : ∀ {m n : ℕ} (κ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] (pol : List Bool → Option (Fin m)) (w : Prefix n),
    parameterWeight κ pol w = pathValidity pol w * ∏ i, coinMass pol w i (κ i) :=
  @ThresholdHC.TypedConfidence.parameter_weight_factor

example : ∀ {m n : ℕ} (κ : Fin m → Measure unitInterval)
    (pol : List Bool → Option (Fin m)) (w : Prefix n),
    0 ≤ parameterWeight κ pol w :=
  @ThresholdHC.TypedConfidence.parameter_weight_nonneg

example : ∀ {m n : ℕ} (κ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] (pol : List Bool → Option (Fin m)),
    ∑ w : Prefix n, parameterWeight κ pol w = 1 :=
  @ThresholdHC.TypedConfidence.parameter_weight_total

example : ∀ {m n : ℕ} (pol : List Bool → Option (Fin m))
    (w : Prefix n) (i : Fin m) (κ : Measure unitInterval),
    0 ≤ coinMass pol w i κ :=
  @ThresholdHC.TypedConfidence.coinMass_nonneg

example : ∀ {m n : ℕ} (pol : List Bool → Option (Fin m))
    (w : Prefix n) (i : Fin m) (κ : Measure unitInterval) [IsProbabilityMeasure κ],
    Integrable (fun p : unitInterval => coinLike pol w i p) κ :=
  @ThresholdHC.TypedConfidence.coinMass_integrable

example : ∀ {m : ℕ} (κ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)]
    (pol : List Bool → Option (Fin m)) (n : ℕ) (i : Fin m),
    parameterLocalWork κ pol n i ≤ n :=
  @ThresholdHC.TypedConfidence.parameter_local_work_le

example : ∀ {m : ℕ} (κ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)]
    (pol : List Bool → Option (Fin m)) (n : ℕ),
    ∑ i : Fin m, parameterLocalWork κ pol n i = parameterExpectedWork κ pol n :=
  @ThresholdHC.TypedConfidence.parameter_total_work

example : ∀ {m : ℕ} (κ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)]
    (pol : List Bool → Option (Fin m)) (n : ℕ),
    ∑ i : Fin m, (parameterLocalWork κ pol n i).toReal =
      (parameterExpectedWork κ pol n).toReal :=
  @ThresholdHC.TypedConfidence.parameter_total_work_real

example : ∀ {m : ℕ} (κ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)]
    (pol : List Bool → Option (Fin m)) (n : ℕ),
    parameterExpectedWork κ pol n ≤ n :=
  @ThresholdHC.TypedConfidence.parameter_expected_work_le

example : ∀ {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r),
    populationParameterLaw μ p₀ p₁ (quarterPrior q r) =
      quarterMix (populationParameterLaw μ p₀ p₁ q) (populationParameterLaw μ p₀ p₁ r) :=
  @ThresholdHC.TypedConfidence.population_parameter_quarter
""".lstrip()
    roots = {'ThresholdHC.TypedConfidence.factor_leaf_log', 'ThresholdHC.TypedConfidence.finite_typed_null_work_kl', 'ThresholdHC.TypedConfidence.quarter_parameter_hybrid_kl', 'ThresholdHC.TypedConfidence.parameter_local_affinity', 'ThresholdHC.TypedConfidence.coinMass_quarter', 'ThresholdHC.TypedConfidence.parameter_hybrid_kl', 'ThresholdHC.TypedConfidence.parameter_word_law', 'ThresholdHC.TypedConfidence.parameter_weight_nonneg', 'ThresholdHC.TypedConfidence.finite_parameter_reference_kl', 'ThresholdHC.TypedConfidence.parameter_total_work', 'ThresholdHC.TypedConfidence.parameter_weight_total', 'ThresholdHC.TypedConfidence.coinMass_nonneg', 'ThresholdHC.TypedConfidence.factorized_kl_sum', 'ThresholdHC.TypedConfidence.parameter_expected_work_le', 'ThresholdHC.TypedConfidence.parameter_one_slot_quarter', 'ThresholdHC.TypedConfidence.parameterTapeLaw_quarter', 'ThresholdHC.TypedConfidence.parameter_local_work_le', 'ThresholdHC.TypedConfidence.parameter_local_word_law', 'ThresholdHC.TypedConfidence.parameter_weight_factor', 'ThresholdHC.TypedConfidence.parameter_total_work_real', 'ThresholdHC.TypedConfidence.population_parameter_quarter', 'ThresholdHC.TypedConfidence.coinMass_integrable'}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.TypedConfidence.NullTransfer"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source, text=True,
                         encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
