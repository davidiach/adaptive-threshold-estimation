"""Audit adaptive-type population information transfer."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.TypedConfidence.Labels
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.CriticalEntropy
open ThresholdHC.ConfidenceTransfer ThresholdHC.TypedConfidence
open ThresholdHC.Tier4 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open Set
local instance : MeasurableSpace (Option Bool) := ⊤
local instance : MeasurableSingletonClass (Option Bool) := ⟨fun _ => trivial⟩

example : ∀ (κ : ℕ → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] (n : ℕ) (pol : List Bool → Option ℕ),
    (Measure.infinitePi (fun i => parameterTapeLaw (κ i))).map
      (fun s => (populationSimulation pol n s).2) =
      finiteWeightMeasure (countableParameterWeight κ pol (n := n)) :=
  @ThresholdHC.TypedConfidence.countable_parameter_word_law

example : ∀ (κ : ℕ → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] {n : ℕ} (pol : List Bool → Option ℕ),
    (∀ w : Prefix n, 0 ≤ countableParameterWeight κ pol w) ∧
      ∑ w : Prefix n, countableParameterWeight κ pol w = 1 :=
  @ThresholdHC.TypedConfidence.countable_parameter_total

example : ∀ (κ : ℕ → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] {n : ℕ} (pol : List Bool → Option ℕ) (w : Prefix n),
    countableParameterWeight κ pol w =
      (∫⁻ s, if (populationSimulation pol n s).2 = w then (1 : ℝ≥0∞) else 0
        ∂Measure.infinitePi (fun i => parameterTapeLaw (κ i))).toReal :=
  @ThresholdHC.TypedConfidence.countable_parameter_weight_integral

example : ∀ {R : Type} [MeasurableSpace R]
    (κ : ℕ → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun r => pol r xs))
    {n : ℕ} (w : Prefix n),
    Measurable (fun r => countableParameterWeight κ (pol r) w) :=
  @ThresholdHC.TypedConfidence.measurable_countableParameterWeight

example : ∀ (κ τ : ℕ → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ i, IsProbabilityMeasure (τ i)]
    {n : ℕ} (pol : List Bool → Option ℕ) (w : Prefix n),
    countableParameterWeight (fun i => ConfidenceTransfer.quarterMix (κ i) (τ i)) pol w ≤
      3^n * countableParameterWeight (fun i => ConfidenceTransfer.quarterMix (τ i) (κ i)) pol w :=
  @ThresholdHC.TypedConfidence.countable_parameter_quarter_ratio

example : ∀ {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (κ : ℕ → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun r => pol r xs)) (n : ℕ),
    Tier5.FiniteKernelRealization ν
      ((ν.prod (Measure.infinitePi (fun i => parameterTapeLaw (κ i)))).map
        (fun z => (z.1,(populationSimulation (pol z.1) n z.2).2)))
      (fun r w => countableParameterWeight κ (pol r) w) :=
  @ThresholdHC.TypedConfidence.seeded_parameter_prefix_kernel

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

example : ∀ {k : ℕ} [NeZero k] (component : Fin k) (coin : ℕ),
    labelType k (typedLabel component coin) = component :=
  @ThresholdHC.TypedConfidence.labelType_typedLabel

example : ∀ {k : ℕ} [NeZero k],
    Function.Injective (fun z : ℕ × Fin k => typedLabel z.2 z.1) :=
  @ThresholdHC.TypedConfidence.typedLabel_injective

example : ∀ {k : ℕ} [NeZero k]
    (pol : List Bool → Option (ℕ × Fin k)) (n : ℕ) (tapes : ℕ → ℕ → Bool),
    (CriticalEntropy.populationSimulation
      (fun xs => (pol xs).map (fun z => typedLabel z.2 z.1)) n tapes).2 =
      (CriticalEntropy.populationSimulation pol n
        (fun z => tapes (typedLabel z.2 z.1))).2 :=
  @ThresholdHC.TypedConfidence.typed_policy_word

example : ∀ {m n : ℕ}
    (pol : List Bool → Option (Fin m)) (w : Prefix n) (i : Fin m)
    (hi : i ∉ queriedCoins pol w) (κ : Measure unitInterval) [IsProbabilityMeasure κ],
    coinMass pol w i κ = 1 :=
  @ThresholdHC.TypedConfidence.coinMass_eq_one_of_not_queried

example : ∀ {m n : ℕ}
    (κ τ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ i, IsProbabilityMeasure (τ i)]
    (pol : List Bool → Option (Fin m)) (w : Prefix n),
    parameterWeight (fun i => quarterMix (κ i) (τ i)) pol w ≤
      3^n * parameterWeight (fun i => quarterMix (τ i) (κ i)) pol w :=
  @ThresholdHC.TypedConfidence.parameter_quarter_ratio

example : ∀ {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r)
    (hqhalf : ∀ x, (q x : ℝ) ≤ 1/2) (hrhalf : ∀ x, (r x : ℝ) ≤ 1/2)
    {K : ℝ} (hK : 0 ≤ K) (hlocal : LocalNullWorkBound μ p₀ p₁ q r K),
    ParameterReferenceBound (populationParameterLaw μ p₀ p₁ q)
      (populationParameterLaw μ p₀ p₁ r) (2*K) :=
  @ThresholdHC.TypedConfidence.parameter_reference_of_null

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

example : ∀ {I : Type} [DecidableEq I]
    (n : ℕ) (pol : List Bool → Option I) (s : I → ℕ → Bool) (t : Fin n),
    ((populationSimulation pol n s).2 t).isSome =
      (pol (histBefore (populationSimulation pol n s).2 t)).isSome :=
  @ThresholdHC.TypedConfidence.populationSimulation_valid

example : ∀ {I : Type} [DecidableEq I]
    (pol : List Bool → Option I) (s : I → ℕ → Bool) (n : ℕ),
    (populationPath pol s n).isSome =
      (pol (processHistory (populationPath pol s) n)).isSome :=
  @ThresholdHC.TypedConfidence.populationPath_valid

example : ∀ {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r),
    populationParameterLaw μ p₀ p₁ (quarterPrior q r) =
      quarterMix (populationParameterLaw μ p₀ p₁ q) (populationParameterLaw μ p₀ p₁ r) :=
  @ThresholdHC.TypedConfidence.population_parameter_quarter

example : ∀ {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (κ : ℕ → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun r => pol r xs)),
    IsProbabilityMeasure (parameterExperimentLaw ν κ pol) :=
  @ThresholdHC.TypedConfidence.parameterExperiment_probability

example : ∀ {R : Type} [MeasurableSpace R]
    (ν : Measure R) (κ : ℕ → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun r => pol r xs)) (n : ℕ),
    (parameterExperimentLaw ν κ pol).map (fun z => (z.1,processPrefix n z.2)) =
      (ν.prod (Measure.infinitePi (fun i => parameterTapeLaw (κ i)))).map
        (fun z => (z.1,(populationSimulation (pol z.1) n z.2).2)) :=
  @ThresholdHC.TypedConfidence.parameter_experiment_prefix

example : ∀ (κ τ : ℕ → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ i, IsProbabilityMeasure (τ i)]
    (pol : List Bool → Option ℕ) (n : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hlocal : ∀ i, ParameterReferenceBound (κ i) (τ i) K),
    klDiv (finiteWeightMeasure (countableParameterWeight (fun i => quarterMix (κ i) (τ i)) pol (n := n)))
      (finiteWeightMeasure (countableParameterWeight (fun i => quarterMix (τ i) (κ i)) pol (n := n))) ≤
      ENNReal.ofReal ((8/3)*K*∑ w : Prefix n,
        countableParameterWeight (fun i => quarterMix (κ i) (τ i)) pol w*workOf w) :=
  @ThresholdHC.TypedConfidence.countable_parameter_reference_kl

example : ∀ {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (κ τ : ℕ → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ i, IsProbabilityMeasure (τ i)]
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun r => pol r xs))
    (n : ℕ) (K : ℝ) (hK : 0 ≤ K) (hlocal : ∀ i, ParameterReferenceBound (κ i) (τ i) K),
    let P := parameterExperimentLaw ν (fun i => quarterMix (κ i) (τ i)) pol
    let Q := parameterExperimentLaw ν (fun i => quarterMix (τ i) (κ i)) pol
    klDiv (P.map (fun z => (z.1,processPrefix n z.2))) (Q.map (fun z => (z.1,processPrefix n z.2))) ≤
      ENNReal.ofReal ((8/3)*K*∫ z, workOf (processPrefix n z.2) ∂P) :=
  @ThresholdHC.TypedConfidence.seeded_parameter_reference_kl

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q r : SignLaw),
    signParameterLaw μ (smoothedSign q r) = quarterMix (signParameterLaw μ q) (signParameterLaw μ r) :=
  @ThresholdHC.TypedConfidence.signParameterLaw_quarter

example : ∀ {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (μ : ℕ → Measure Gap) [∀ i, IsProbabilityMeasure (μ i)] (q r : ℕ → SignLaw)
    (hqhalf : ∀ i d, (q i).val d ≤ 1/2) (hrhalf : ∀ i d, (r i).val d ≤ 1/2)
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun u => pol u xs))
    (K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hlocal : ∀ i, LocalNullWorkBound (μ i) (gapParameter false) (gapParameter true)
      (signUnit (q i)) (signUnit (r i)) K)
    (hw : (∫⁻ z, totalProcessWork z.2
      ∂parameterExperimentLaw ν (fun i => signParameterLaw (μ i) (smoothedSign (q i) (r i))) pol) ≤ ENNReal.ofReal B)
    (hw' : (∫⁻ z, totalProcessWork z.2
      ∂parameterExperimentLaw ν (fun i => signParameterLaw (μ i) (smoothedSign (r i) (q i))) pol) < ∞),
    klDiv (parameterExperimentLaw ν (fun i => signParameterLaw (μ i) (smoothedSign (q i) (r i))) pol)
      (parameterExperimentLaw ν (fun i => signParameterLaw (μ i) (smoothedSign (r i) (q i))) pol) ≤
      ENNReal.ofReal ((16/3)*K*B) :=
  @ThresholdHC.TypedConfidence.stopped_typed_null_work_kl

example : ∀ {R : Type} [MeasurableSpace R]
    (ν : Measure R) (κ : ℕ → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun r => pol r xs)),
    ∀ᵐ z ∂parameterExperimentLaw ν κ pol, ∀ n,
      (z.2 n).isSome = (pol z.1 (processHistory z.2 n)).isSome :=
  @ThresholdHC.TypedConfidence.parameter_valid_ae

example : ∀ {R : Type} [MeasurableSpace R]
    (ν : Measure R) (κ : ℕ → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun r => pol r xs))
    (hw : (∫⁻ z, totalProcessWork z.2 ∂parameterExperimentLaw ν κ pol) < ∞),
    ∀ᵐ z ∂parameterExperimentLaw ν κ pol, z ∈ ⋃ n, stoppedFullSet (Tier5.stoppingFlagPolicy pol) n :=
  @ThresholdHC.TypedConfidence.parameter_stopped_cover

example : ∀ {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (κ τ : ℕ → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ i, IsProbabilityMeasure (τ i)]
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun r => pol r xs))
    (hw : (∫⁻ z, totalProcessWork z.2 ∂parameterExperimentLaw ν κ pol) < ∞)
    (hw' : (∫⁻ z, totalProcessWork z.2 ∂parameterExperimentLaw ν τ pol) < ∞),
    klDiv (parameterExperimentLaw ν κ pol) (parameterExperimentLaw ν τ pol) =
      ⨆ n, klDiv
        ((parameterExperimentLaw ν κ pol).map (fun z => (z.1,processPrefix n z.2)))
        ((parameterExperimentLaw ν τ pol).map (fun z => (z.1,processPrefix n z.2))) :=
  @ThresholdHC.TypedConfidence.stopped_parameter_kl_eq_iSup

example : ∀ {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (κ τ : ℕ → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ i, IsProbabilityMeasure (τ i)]
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun r => pol r xs))
    (K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B) (hlocal : ∀ i, ParameterReferenceBound (κ i) (τ i) K)
    (hw : (∫⁻ z, totalProcessWork z.2
      ∂parameterExperimentLaw ν (fun i => quarterMix (κ i) (τ i)) pol) ≤ ENNReal.ofReal B)
    (hw' : (∫⁻ z, totalProcessWork z.2
      ∂parameterExperimentLaw ν (fun i => quarterMix (τ i) (κ i)) pol) < ∞),
    klDiv (parameterExperimentLaw ν (fun i => quarterMix (κ i) (τ i)) pol)
      (parameterExperimentLaw ν (fun i => quarterMix (τ i) (κ i)) pol) ≤
      ENNReal.ofReal ((8/3)*K*B) :=
  @ThresholdHC.TypedConfidence.stopped_parameter_reference_kl

example : ∀ {m n : ℕ}
    (κ : Fin m → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (pol : List Bool → Option (Fin m)),
    parameterExpectedWork κ pol n =
      ∑ w : Fin n → Option Bool, ENNReal.ofReal
        (parameterWeight κ pol w)*ENNReal.ofReal (ThresholdHC.workOf w) :=
  @ThresholdHC.TypedConfidence.parameter_work_law

example : ∀ {m n : ℕ}
    (κ : Fin m → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (pol : List Bool → Option (Fin m)),
    (parameterExpectedWork κ pol n).toReal =
      ∑ w : Fin n → Option Bool, parameterWeight κ pol w*ThresholdHC.workOf w :=
  @ThresholdHC.TypedConfidence.parameter_work_real
""".lstrip()
    roots = {
        'ThresholdHC.TypedConfidence.coinMass_eq_one_of_not_queried',
        'ThresholdHC.TypedConfidence.coinMass_integrable',
        'ThresholdHC.TypedConfidence.coinMass_nonneg',
        'ThresholdHC.TypedConfidence.coinMass_quarter',
        'ThresholdHC.TypedConfidence.countable_parameter_quarter_ratio',
        'ThresholdHC.TypedConfidence.countable_parameter_reference_kl',
        'ThresholdHC.TypedConfidence.countable_parameter_total',
        'ThresholdHC.TypedConfidence.countable_parameter_weight_integral',
        'ThresholdHC.TypedConfidence.countable_parameter_word_law',
        'ThresholdHC.TypedConfidence.factor_leaf_log',
        'ThresholdHC.TypedConfidence.factorized_kl_sum',
        'ThresholdHC.TypedConfidence.finite_parameter_reference_kl',
        'ThresholdHC.TypedConfidence.finite_typed_null_work_kl',
        'ThresholdHC.TypedConfidence.labelType_typedLabel',
        'ThresholdHC.TypedConfidence.measurable_countableParameterWeight',
        'ThresholdHC.TypedConfidence.parameterExperiment_probability',
        'ThresholdHC.TypedConfidence.parameterTapeLaw_quarter',
        'ThresholdHC.TypedConfidence.parameter_expected_work_le',
        'ThresholdHC.TypedConfidence.parameter_experiment_prefix',
        'ThresholdHC.TypedConfidence.parameter_hybrid_kl',
        'ThresholdHC.TypedConfidence.parameter_local_affinity',
        'ThresholdHC.TypedConfidence.parameter_local_word_law',
        'ThresholdHC.TypedConfidence.parameter_local_work_le',
        'ThresholdHC.TypedConfidence.parameter_one_slot_quarter',
        'ThresholdHC.TypedConfidence.parameter_quarter_ratio',
        'ThresholdHC.TypedConfidence.parameter_reference_of_null',
        'ThresholdHC.TypedConfidence.parameter_stopped_cover',
        'ThresholdHC.TypedConfidence.parameter_total_work',
        'ThresholdHC.TypedConfidence.parameter_total_work_real',
        'ThresholdHC.TypedConfidence.parameter_valid_ae',
        'ThresholdHC.TypedConfidence.parameter_weight_factor',
        'ThresholdHC.TypedConfidence.parameter_weight_nonneg',
        'ThresholdHC.TypedConfidence.parameter_weight_total',
        'ThresholdHC.TypedConfidence.parameter_word_law',
        'ThresholdHC.TypedConfidence.parameter_work_law',
        'ThresholdHC.TypedConfidence.parameter_work_real',
        'ThresholdHC.TypedConfidence.populationPath_valid',
        'ThresholdHC.TypedConfidence.populationSimulation_valid',
        'ThresholdHC.TypedConfidence.population_parameter_quarter',
        'ThresholdHC.TypedConfidence.quarter_parameter_hybrid_kl',
        'ThresholdHC.TypedConfidence.seeded_parameter_prefix_kernel',
        'ThresholdHC.TypedConfidence.seeded_parameter_reference_kl',
        'ThresholdHC.TypedConfidence.signParameterLaw_quarter',
        'ThresholdHC.TypedConfidence.stopped_parameter_kl_eq_iSup',
        'ThresholdHC.TypedConfidence.stopped_parameter_reference_kl',
        'ThresholdHC.TypedConfidence.stopped_typed_null_work_kl',
        'ThresholdHC.TypedConfidence.typedLabel_injective',
        'ThresholdHC.TypedConfidence.typed_policy_word',
    }
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.TypedConfidence.Labels"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source, text=True,
                         encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
