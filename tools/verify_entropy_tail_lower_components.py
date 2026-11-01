"""Audit supporting lemmas for the unfinished entropy-tail lower bound.

Default: rebuild the entire local dependency closure. --cached-dependencies
rebuilds only the thirty-seven supporting modules and records the reused artifact hashes.
Both modes check the frozen weighted-sign target, the exact certificate
reduction, and every new declaration's transitive axioms. Neither mode proves
the statistical lower bound or the two-sided entropy-tail/quantile laws.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys

from verify_blind_upper_components import (
    DECLARATION, FORBIDDEN, module_path, sha, strip_comments,
    validate_dependency_freeze, validate_reports,
)
from verify_entropy_tail_components import dependency_order
from verify_entropy_tail import validate_sources as validate_canonical_sources
from stopping_program_lock import validate_stopping_specification

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
SOURCE = LEAN / "ThresholdHC/EntropyTailLower"
PREFIX = "ThresholdHC.EntropyTailLower."
MODULES = ("Specification", "WeightedOverlap", "WeightedSign", "WeightedEstimation",
           "AnnularWork", "AnnularEstimation", "CertificateReduction", "FractionalPrior",
           "GeneralGoodGaps", "PopulationAnnular", "ActivationGate", "GateLikelihood", "FairGateWork",
           "GateMeasure", "GatedOutput", "FiniteAverageProcedure", "GateAverage",
           "PopulationGateAverage", "EarlyLikelihood", "EarlyOutput", "EarlyMean", "GatedGoodGaps",
           "GateMomentFloor", "GatedAnnular", "CertificateCentering", "FlowOneCoin", "CertificateOneCoin",
           "PopulationPullback", "CertificateAnnular",
           "ComponentPriors", "ComponentLocalization", "LocalizationAlgebra", "LocalizedAnnular",
           "CanonicalBands", "DyadicMass", "EntropyIncrement", "FiniteSelection")
FREEZE = ROOT / "tools/entropy_tail_lower_specification_freeze.json"
FROZEN = {"lean/ThresholdHC/EntropyTailLower/Specification.lean":
          "dfa2367c933f1cdbeeb82ecca9e92ca8a512d98de28a54cdee9c741b7acd3461"}
EXACT_TARGETS = {
    PREFIX + "weighted_sign_entropy": PREFIX + "WeightedSignEntropyStatement",
    PREFIX + "entropy_tail_lower_iff_certificate_lower":
        "ThresholdHC.EntropyTail.EntropyTailLowerStatement ↔ "
        "(∃ c : ℝ, 0 < c ∧ ∀ (μ : MeasureTheory.Measure ThresholdHC.Tier6.Gap) "
        "[MeasureTheory.IsProbabilityMeasure μ] (ρ B : ℝ), "
        "0 < ρ → ρ ≤ 1/4 → 0 < B → ∀ (N : ℕ), 0 < N → "
        "∀ C : ThresholdHC.StoppingProgram.Certificate N, "
        "ThresholdHC.StoppingProgram.Feasible μ ρ B C → "
        "ENNReal.ofReal c * ThresholdHC.EntropyTail.selection μ ρ B ≤ "
        "ThresholdHC.StoppingProgram.certificateSquared C ^ (1/2 : ℝ))",
    PREFIX + "population_good_gaps_general": """
        ∀ {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
        (μ : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure μ]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (p₀ p₁ : D → unitInterval), Measurable p₀ → Measurable p₁ →
        ∀ (ρ : unitInterval), 0 < (ρ:ℝ) → (ρ:ℝ) ≤ 1/4 →
        ∀ (m : ℝ), 2*(ρ:ℝ)/3 ≤ m → ∀ (A : CriticalEntropy.StoppedProcedure R ℝ),
        CriticalEntropy.CappedPopulationGuarantee μ ν p₀ p₁ A (ρ:ℝ) m →
        ∃ G : Set D, MeasurableSet G ∧ μ.real Gᶜ ≤ 70*m ∧
          ∀ d ∈ G, CriticalEntropy.PopulationGoodGap ν p₀ p₁ A (ρ:ℝ) m d
        """,
    PREFIX + "population_annular_entropy": """
        ∀ {R : Type} [MeasurableSpace R]
        (μ : MeasureTheory.Measure CriticalEntropy.EntropyGap) [MeasureTheory.IsProbabilityMeasure μ]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (A : CriticalEntropy.StoppedProcedure R ℝ) (ρ : unitInterval),
        0 < (ρ:ℝ) → (ρ:ℝ) ≤ 1/4 → ∀ (m : ℝ), 0 ≤ m →
        CriticalEntropy.CappedPopulationGuarantee μ ν
          (fun d => CriticalEntropy.signParameter d false)
          (fun d => CriticalEntropy.signParameter d true) A (ρ:ℝ) m →
        ∀ {K : ℕ} (I : Fin K → Set CriticalEntropy.EntropyGap) (b : Fin K → ℝ),
        (∀ i, 0 < b i) → (∀ i, MeasurableSet (I i)) →
        Pairwise (fun i j => Disjoint (I i) (I j)) →
        (∀ i d, d ∈ I i → b i/2 < (d:ℝ) ∧ (d:ℝ) ≤ b i) →
        (∀ i j, j.val = i.val+1 → 4*b j ≤ b i) →
        (∀ i, 140*m ≤ μ.real (I i)) →
        (ρ:ℝ)*EntropyTailQuantile.costEntropy (fun i => μ.real (I i)/(b i)^2) ≤
          33554432*m*(CriticalEntropy.populationExpectedWork μ ν
            (fun d => CriticalEntropy.signParameter d false)
            (fun d => CriticalEntropy.signParameter d true) (fun _ => 0) A).toReal
        """,
    PREFIX + "activationGateCost_min": """
        ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
        (A : CriticalEntropy.StoppedProcedure R E) (M H : ℕ) (z : R × (ℕ → Bool)),
        (EntropyTailLower.activationGateCost A M H z:ℕ∞) =
          min (A.stop z) (EntropyTailLower.boundaryGateCost M H z.2:ℕ∞)
        """,
    PREFIX + "activationGate_accepts_iff": """
        ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
        (A : CriticalEntropy.StoppedProcedure R E) (M H : ℕ) (z : R × (ℕ → Bool)),
        (EntropyTailLower.activationGate A M H).output z = true ↔
          (EntropyTailLower.boundaryGateCost M H z.2:ℕ∞) ≤ A.stop z
        """,
    PREFIX + "activationGate_prefix_likelihood": """
        ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
        (A : CriticalEntropy.StoppedProcedure R E) (a d : ℝ),
        0 < a → a ≤ 1/4 → |d| ≤ a → ∀ (z : R × (ℕ → Bool)),
        let n := EntropyTailLower.activationGateCost A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ z
        let k := CriticalEntropy.wordHeads (Tier2.tapePrefix n z.2)
        Real.exp (-12) ≤ EntropyTailLower.gatePrefixLikelihood d n k ∧
          EntropyTailLower.gatePrefixLikelihood d n k ≤ Real.exp 12
        """,
    PREFIX + "activationGate_fair_square_identity": """
        ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (A : CriticalEntropy.StoppedProcedure R E) (M H : ℕ),
        (∫ z, (EntropyTailLower.tapeBalance (EntropyTailLower.activationGateCost A M H z) z.2:ℝ)^2
          ∂ν.prod (Tier2.tapeMeasure ⟨1/2,by norm_num⟩)) =
          ∫ z, (EntropyTailLower.activationGateCost A M H z:ℝ)
            ∂ν.prod (Tier2.tapeMeasure ⟨1/2,by norm_num⟩)
        """,
    PREFIX + "activationGate_fair_scaled_probability": """
        ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (A : CriticalEntropy.StoppedProcedure R E) (a : ℝ), 0 < a →
        (ν.prod (Tier2.tapeMeasure ⟨1/2,by norm_num⟩)).real
          {z | (EntropyTailLower.activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true} ≤
          2*a^2*(CriticalEntropy.expectedStoppedProcedureWork ν ⟨1/2,by norm_num⟩
            (EntropyTailLower.activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊)).toReal
        """,
    PREFIX + "activationGate_transcript_comparison": """
        ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (A : CriticalEntropy.StoppedProcedure R E) (a : ℝ), 0 < a → a ≤ 1/4 →
        ∀ (p : unitInterval), |(p:ℝ)-1/2| ≤ a →
        ENNReal.ofReal (Real.exp (-12)) • EntropyTailLower.coinTranscriptLaw ν ⟨1/2,by norm_num⟩
          (EntropyTailLower.activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ⌈(a^2)⁻¹⌉₊ ≤
            EntropyTailLower.coinTranscriptLaw ν p
              (EntropyTailLower.activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ⌈(a^2)⁻¹⌉₊ ∧
          EntropyTailLower.coinTranscriptLaw ν p
            (EntropyTailLower.activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ⌈(a^2)⁻¹⌉₊ ≤
            ENNReal.ofReal (Real.exp 12) • EntropyTailLower.coinTranscriptLaw ν ⟨1/2,by norm_num⟩
              (EntropyTailLower.activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ⌈(a^2)⁻¹⌉₊
        """,
    PREFIX + "activationGate_work_comparison": """
        ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (A : CriticalEntropy.StoppedProcedure R E) (a : ℝ), 0 < a → a ≤ 1/4 →
        ∀ (p : unitInterval), |(p:ℝ)-1/2| ≤ a →
        ENNReal.ofReal (Real.exp (-12))*CriticalEntropy.expectedStoppedProcedureWork ν ⟨1/2,by norm_num⟩
          (EntropyTailLower.activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ≤
            CriticalEntropy.expectedStoppedProcedureWork ν p
              (EntropyTailLower.activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ∧
          CriticalEntropy.expectedStoppedProcedureWork ν p
            (EntropyTailLower.activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ≤
            ENNReal.ofReal (Real.exp 12)*CriticalEntropy.expectedStoppedProcedureWork ν ⟨1/2,by norm_num⟩
              (EntropyTailLower.activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊)
        """,
    PREFIX + "activationGate_probability_comparison": """
        ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (A : CriticalEntropy.StoppedProcedure R E) (a : ℝ), 0 < a → a ≤ 1/4 →
        ∀ (p : unitInterval), |(p:ℝ)-1/2| ≤ a →
        ENNReal.ofReal (Real.exp (-12))*(ν.prod (Tier2.tapeMeasure ⟨1/2,by norm_num⟩))
          {z | (EntropyTailLower.activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true} ≤
          (ν.prod (Tier2.tapeMeasure p))
            {z | (EntropyTailLower.activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true} ∧
          (ν.prod (Tier2.tapeMeasure p))
            {z | (EntropyTailLower.activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true} ≤
            ENNReal.ofReal (Real.exp 12)*(ν.prod (Tier2.tapeMeasure ⟨1/2,by norm_num⟩))
              {z | (EntropyTailLower.activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true}
        """,
    PREFIX + "activationGate_fair_probability_le_biased_work": """
        ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (A : CriticalEntropy.StoppedProcedure R E) (a : ℝ), 0 < a → a ≤ 1/4 →
        ∀ (p : unitInterval), |(p:ℝ)-1/2| ≤ a →
        (ν.prod (Tier2.tapeMeasure ⟨1/2,by norm_num⟩))
          {z | (EntropyTailLower.activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true} ≤
          ENNReal.ofReal (2*Real.exp 12*a^2)*CriticalEntropy.expectedStoppedProcedureWork ν p A
        """,
    PREFIX + "gatedProcedure_output": """
        ∀ {R : Type} [MeasurableSpace R] (A : CriticalEntropy.StoppedProcedure R ℝ) (M H : ℕ),
        (EntropyTailLower.gatedProcedure A M H).output =
          {z | (EntropyTailLower.activationGate A M H).output z = true}.indicator A.output
        """,
    PREFIX + "averageProcedure_mean": """
        ∀ {R : Type} [MeasurableSpace R]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν] (p : unitInterval)
        (A : CriticalEntropy.StoppedProcedure R ℝ),
        CriticalEntropy.expectedStoppedProcedureWork ν p A ≠ ∞ →
        CriticalEntropy.conditionalSecondMoment ν p A ≠ ∞ → ∀ (n : ℕ),
        CriticalEntropy.conditionalMean (MeasureTheory.Measure.pi (fun _ : Fin (n+1) => ν)) p
          (EntropyTailLower.averageProcedure A n) = CriticalEntropy.conditionalMean ν p A
        """,
    PREFIX + "gateAverage_work_le": """
        ∀ {R : Type} [MeasurableSpace R]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν] (p : unitInterval)
        (A : CriticalEntropy.StoppedProcedure R ℝ),
        CriticalEntropy.expectedStoppedProcedureWork ν p A ≠ ∞ → ∀ (M H : ℕ) (q : ℝ),
        0 < q → q ≤ 1 →
        CriticalEntropy.expectedStoppedProcedureWork
          (MeasureTheory.Measure.pi (fun _ : Fin ((EntropyTailLower.gateBatchCount q-1)+1) => ν)) p
          (EntropyTailLower.gateAverage A M H q) ≤
          ENNReal.ofReal (2/q)*CriticalEntropy.expectedStoppedProcedureWork ν p A
        """,
    PREFIX + "scaled_gateAverage_secondMoment_le": """
        ∀ {R : Type} [MeasurableSpace R]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (A : CriticalEntropy.StoppedProcedure R ℝ) (a : ℝ), 0 < a → a ≤ 1/4 →
        0 < EntropyTailLower.fairActivation ν A a →
        ∀ (p : unitInterval), |(p:ℝ)-1/2| ≤ a →
        CriticalEntropy.expectedStoppedProcedureWork ν p A ≠ ∞ →
        CriticalEntropy.conditionalSecondMoment ν p A ≠ ∞ →
        CriticalEntropy.conditionalSecondMoment
          (MeasureTheory.Measure.pi (fun _ : Fin ((EntropyTailLower.gateBatchCount
            (EntropyTailLower.fairActivation ν A a)-1)+1) => ν)) p
          (EntropyTailLower.gateAverage A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ (EntropyTailLower.fairActivation ν A a)) ≤
          ENNReal.ofReal ((1+Real.exp 12)*EntropyTailLower.fairActivation ν A a)*
            CriticalEntropy.conditionalSecondMoment ν p A
        """,
    PREFIX + "population_gateAverage_uniform": """
        ∀ {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
        (μ : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure μ]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (p₀ p₁ : D → unitInterval), Measurable p₀ → Measurable p₁ →
        ∀ (A : CriticalEntropy.StoppedProcedure R ℝ) (ρ : unitInterval),
        0 < (ρ:ℝ) → (ρ:ℝ) ≤ 1/4 → ∀ (m : ℝ),
        CriticalEntropy.CappedPopulationGuarantee μ ν p₀ p₁ A (ρ:ℝ) m →
        ∀ (a : ℝ), 0 < a → a ≤ 1/4 →
        (∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a ∧ |(p₁ d:ℝ)-1/2| ≤ a) →
        0 < EntropyTailLower.fairActivation ν A a →
        let β := EntropyTailLower.fairActivation ν A a
        let Z := EntropyTailLower.gateAverage A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ β
        let η := MeasureTheory.Measure.pi (fun _ : Fin ((EntropyTailLower.gateBatchCount β-1)+1) => ν)
        ∀ q, CriticalEntropy.CappedPrior μ (ρ:ℝ) q →
          CriticalEntropy.populationSecondMoment μ η p₀ p₁ q Z ≤
            ENNReal.ofReal (((1+Real.exp 12)*β)*m) ∧
          CriticalEntropy.populationExpectedWork μ η p₀ p₁ q Z ≠ ∞
        """,
    PREFIX + "population_gateAverage_tradeoff": """
        ∀ {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
        (μ : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure μ]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (p₀ p₁ : D → unitInterval), Measurable p₀ → Measurable p₁ →
        ∀ (A : CriticalEntropy.StoppedProcedure R ℝ) (ρ : unitInterval),
        0 < (ρ:ℝ) → (ρ:ℝ) ≤ 1/4 → ∀ (m : ℝ), 0 ≤ m →
        CriticalEntropy.CappedPopulationGuarantee μ ν p₀ p₁ A (ρ:ℝ) m →
        ∀ (a : ℝ), 0 < a → a ≤ 1/4 →
        (∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a ∧ |(p₁ d:ℝ)-1/2| ≤ a) →
        0 < EntropyTailLower.fairActivation ν A a →
        let β := EntropyTailLower.fairActivation ν A a
        let Z := EntropyTailLower.gateAverage A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ β
        let η := MeasureTheory.Measure.pi (fun _ : Fin ((EntropyTailLower.gateBatchCount β-1)+1) => ν)
        let mZ := (1+Real.exp 12)*β*m
        mZ ≤ 2*Real.exp 12*(1+Real.exp 12)*a^2*m*
          (CriticalEntropy.populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal ∧
        mZ*(CriticalEntropy.populationExpectedWork μ η p₀ p₁ (fun _ => 0) Z).toReal ≤
          2*(1+Real.exp 12)*m*(CriticalEntropy.populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal
        """,
    PREFIX + "activationGate_prefix_likelihood_difference": """
        ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
        (A : CriticalEntropy.StoppedProcedure R E) (a d : ℝ),
        0 < a → a ≤ 1/4 → |d| ≤ a → ∀ (z : R × (ℕ → Bool)),
        let n := EntropyTailLower.activationGateCost A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ z
        let k := CriticalEntropy.wordHeads (Tier2.tapePrefix n z.2)
        |EntropyTailLower.gatePrefixLikelihood d n k-EntropyTailLower.gatePrefixLikelihood (-d) n k| ≤
          8*Real.exp 12*|d| * |(EntropyTailLower.tapeBalance n z.2:ℝ)|
        """,
    PREFIX + "earlyProcedure_stop": """
        ∀ {R : Type} [MeasurableSpace R] (A : CriticalEntropy.StoppedProcedure R ℝ) (M H : ℕ),
        (EntropyTailLower.earlyProcedure A M H).stop = (EntropyTailLower.activationGate A M H).stop
        """,
    PREFIX + "early_gated_mean_sum": """
        ∀ {R : Type} [MeasurableSpace R]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν] (p : unitInterval)
        (A : CriticalEntropy.StoppedProcedure R ℝ),
        CriticalEntropy.conditionalSecondMoment ν p A ≠ ∞ → ∀ (M H : ℕ),
        CriticalEntropy.conditionalMean ν p (EntropyTailLower.earlyProcedure A M H)+
          CriticalEntropy.conditionalMean ν p (EntropyTailLower.gatedProcedure A M H) =
            CriticalEntropy.conditionalMean ν p A
        """,
    PREFIX + "population_early_mean_difference": """
        ∀ {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
        (μ : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure μ]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (p₀ p₁ : D → unitInterval), Measurable p₀ → Measurable p₁ →
        ∀ (A : CriticalEntropy.StoppedProcedure R ℝ) (a : ℝ), 0 < a → a ≤ 1/4 →
        (∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a) →
        CriticalEntropy.populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A ≠ ∞ →
        CriticalEntropy.populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A ≠ ∞ →
        ∀ (p q : unitInterval), |(p:ℝ)-1/2| ≤ a → (p:ℝ)+(q:ℝ) = 1 →
        (CriticalEntropy.conditionalMean ν p (EntropyTailLower.earlyProcedure A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊)-
          CriticalEntropy.conditionalMean ν q (EntropyTailLower.earlyProcedure A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊))^2 ≤
          64*Real.exp 48*a^2*(CriticalEntropy.populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A).toReal*
            (CriticalEntropy.populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal
        """,
    PREFIX + "fair_activation_positive_of_small_work": """
        ∀ {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
        (μ : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure μ]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (p₀ p₁ : D → unitInterval), Measurable p₀ → Measurable p₁ →
        ∀ (A : CriticalEntropy.StoppedProcedure R ℝ) (ρ : unitInterval),
        0 < (ρ:ℝ) → (ρ:ℝ) ≤ 1/4 → ∀ (m : ℝ), 0 ≤ m →
        CriticalEntropy.CappedPopulationGuarantee μ ν p₀ p₁ A (ρ:ℝ) m →
        ∀ (a : ℝ), 0 < a → a ≤ 1/4 →
        (∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a ∧ (p₀ d:ℝ)+(p₁ d:ℝ) = 1) →
        64*Real.exp 48*a^2*m*(CriticalEntropy.populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal ≤ 1/16 →
        0 < (ν.prod (Tier2.tapeMeasure ⟨1/2,by norm_num⟩)).real
          {z | (EntropyTailLower.activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true}
        """,
    PREFIX + "population_gate_good_gaps": """
        ∀ {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
        (μ : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure μ]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (p₀ p₁ : D → unitInterval), Measurable p₀ → Measurable p₁ →
        ∀ (A : CriticalEntropy.StoppedProcedure R ℝ) (ρ : unitInterval),
        0 < (ρ:ℝ) → (ρ:ℝ) ≤ 1/4 → ∀ (m : ℝ), 0 < m →
        CriticalEntropy.CappedPopulationGuarantee μ ν p₀ p₁ A (ρ:ℝ) m →
        ∀ (a : ℝ), 0 < a → a ≤ 1/4 →
        (∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a ∧ (p₀ d:ℝ)+(p₁ d:ℝ) = 1) →
        64*Real.exp 48*a^2*m*(CriticalEntropy.populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal ≤ 1/64 →
        let β := EntropyTailLower.fairActivation ν A a
        let Z := EntropyTailLower.gateAverage A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ β
        let η := MeasureTheory.Measure.pi (fun _ : Fin ((EntropyTailLower.gateBatchCount β-1)+1) => ν)
        let mZ := (1+Real.exp 12)*β*m
        0 < β ∧ ∃ G : Set D, MeasurableSet G ∧ μ.real Gᶜ ≤ 64*mZ+4*(ρ:ℝ) ∧
          ∀ d ∈ G, CriticalEntropy.PopulationGoodGap η p₀ p₁ Z (ρ:ℝ) mZ d
        """,
    PREFIX + "population_gate_moment_floor": """
        ∀ {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
        (μ : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure μ]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (p₀ p₁ : D → unitInterval), Measurable p₀ → Measurable p₁ →
        ∀ (A : CriticalEntropy.StoppedProcedure R ℝ) (ρ : unitInterval),
        0 < (ρ:ℝ) → (ρ:ℝ) ≤ 1/4 → ∀ (m : ℝ), 0 < m →
        CriticalEntropy.CappedPopulationGuarantee μ ν p₀ p₁ A (ρ:ℝ) m →
        ∀ (a : ℝ), 0 < a → a ≤ 1/4 →
        (∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a ∧ (p₀ d:ℝ)+(p₁ d:ℝ) = 1) →
        64*Real.exp 48*a^2*m*(CriticalEntropy.populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal ≤ 1/64 →
        (ρ:ℝ)/2 ≤ (1+Real.exp 12)*EntropyTailLower.fairActivation ν A a*m
        """,
    PREFIX + "population_gate_good_gaps_mass": """
        ∀ {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
        (μ : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure μ]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (p₀ p₁ : D → unitInterval), Measurable p₀ → Measurable p₁ →
        ∀ (A : CriticalEntropy.StoppedProcedure R ℝ) (ρ : unitInterval),
        0 < (ρ:ℝ) → (ρ:ℝ) ≤ 1/4 → ∀ (m : ℝ), 0 < m →
        CriticalEntropy.CappedPopulationGuarantee μ ν p₀ p₁ A (ρ:ℝ) m →
        ∀ (a : ℝ), 0 < a → a ≤ 1/4 →
        (∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a ∧ (p₀ d:ℝ)+(p₁ d:ℝ) = 1) →
        64*Real.exp 48*a^2*m*(CriticalEntropy.populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal ≤ 1/64 →
        let β := EntropyTailLower.fairActivation ν A a
        let Z := EntropyTailLower.gateAverage A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ β
        let η := MeasureTheory.Measure.pi (fun _ : Fin ((EntropyTailLower.gateBatchCount β-1)+1) => ν)
        let mZ := (1+Real.exp 12)*β*m
        0 < β ∧ ∃ G : Set D, MeasurableSet G ∧ μ.real Gᶜ ≤ 72*mZ ∧
          ∀ d ∈ G, CriticalEntropy.PopulationGoodGap η p₀ p₁ Z (ρ:ℝ) mZ d
        """,
    PREFIX + "population_gated_annular_saturation": """
        ∀ {R : Type} [MeasurableSpace R]
        (μ : MeasureTheory.Measure CriticalEntropy.EntropyGap) [MeasureTheory.IsProbabilityMeasure μ]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (A : CriticalEntropy.StoppedProcedure R ℝ) (ρ : unitInterval),
        0 < (ρ:ℝ) → (ρ:ℝ) ≤ 1/4 → ∀ (m : ℝ), 0 ≤ m →
        CriticalEntropy.CappedPopulationGuarantee μ ν
          (fun d => CriticalEntropy.signParameter d false)
          (fun d => CriticalEntropy.signParameter d true) A (ρ:ℝ) m →
        ∀ (a : ℝ), 0 < a → a ≤ 1/4 →
        (∀ᵐ (d : CriticalEntropy.EntropyGap) ∂μ, (d:ℝ) ≤ a) →
        ∀ {K : ℕ} (I : Fin K → Set CriticalEntropy.EntropyGap) (b : Fin K → ℝ),
        (∀ i, 0 < b i) → (∀ i, MeasurableSet (I i)) →
        Pairwise (fun i j => Disjoint (I i) (I j)) →
        (∀ i d, d ∈ I i → b i/2 < (d:ℝ) ∧ (d:ℝ) ≤ b i) →
        (∀ i j, j.val = i.val+1 → 4*b j ≤ b i) →
        ∀ (s : ℝ), s ≤ 1 → (∀ i, s ≤ μ.real (I i)) →
        min (s/a^2) ((ρ:ℝ)*EntropyTailQuantile.costEntropy (fun i => μ.real (I i)/(b i)^2)) ≤
          1073741824*Real.exp 48*m*(CriticalEntropy.populationExpectedWork μ ν
            (fun d => CriticalEntropy.signParameter d false)
            (fun d => CriticalEntropy.signParameter d true) (fun _ => 0) A).toReal
        """,
    PREFIX + "centeredCertificate_feasible": """
        ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ]
        (ρ B : ℝ), 0 ≤ ρ → ∀ (C : StoppingProgram.Certificate N),
        StoppingProgram.Feasible μ ρ B C → 0 < StoppingProgram.intensity C.flow →
        StoppingProgram.Feasible μ ρ B (EntropyTailLower.centeredCertificate μ C)
        """,
    PREFIX + "centeredCertificate_squared": """
        ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) (C : StoppingProgram.Certificate N),
        StoppingProgram.certificateSquared (EntropyTailLower.centeredCertificate μ C) =
          4*StoppingProgram.certificateSquared C
        """,
    PREFIX + "certificate_large_bias_or_positive_intensity": """
        ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ]
        (ρ B : ℝ), 0 ≤ ρ → ρ ≤ 1 → ∀ (C : StoppingProgram.Certificate N),
        StoppingProgram.Feasible μ ρ B C → ρ/2 ≤ C.bias ∨ 0 < StoppingProgram.intensity C.flow
        """,
    PREFIX + "flowCoinProcedure_population_mean": """
        ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ]
        (q : Tier6.SignLaw) (hN : 0 < N) (f : StoppingProgram.Flow N),
        StoppingProgram.FlowCone f →
        CriticalEntropy.populationMean μ (EntropyTailLower.flowCoinSeedLaw f)
          (ObservableSimulation.gapParameter false) (ObservableSimulation.gapParameter true)
          (ObservableSimulation.signUnit q) (EntropyTailLower.flowCoinProcedure hN f) =
            StoppingProgram.countMean μ q f.outputWeight
        """,
    PREFIX + "flowCoinProcedure_population_moment": """
        ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ]
        (q : Tier6.SignLaw) (hN : 0 < N) (f : StoppingProgram.Flow N),
        StoppingProgram.FlowCone f →
        CriticalEntropy.populationSecondMoment μ (EntropyTailLower.flowCoinSeedLaw f)
          (ObservableSimulation.gapParameter false) (ObservableSimulation.gapParameter true)
          (ObservableSimulation.signUnit q) (EntropyTailLower.flowCoinProcedure hN f) ≤
            ENNReal.ofReal (StoppingProgram.intensity f*StoppingProgram.countMean μ q f.momentWeight)
        """,
    PREFIX + "flowCoinProcedure_population_work": """
        ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ]
        (q : Tier6.SignLaw) (hN : 0 < N) (f : StoppingProgram.Flow N),
        StoppingProgram.FlowCone f → 0 < StoppingProgram.intensity f →
        CriticalEntropy.populationExpectedWork μ (EntropyTailLower.flowCoinSeedLaw f)
          (ObservableSimulation.gapParameter false) (ObservableSimulation.gapParameter true)
          (ObservableSimulation.signUnit q) (EntropyTailLower.flowCoinProcedure hN f) =
            ENNReal.ofReal (StoppingProgram.countMean μ q f.continueWeight/StoppingProgram.intensity f)
        """,
    PREFIX + "certificate_large_bias_lower": """
        ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) (ρ B : ℝ) (C : StoppingProgram.Certificate N),
        0 ≤ C.bias → 0 ≤ C.variance → ρ/128 ≤ C.bias →
        ENNReal.ofReal (1/128:ℝ)*EntropyTail.selection μ ρ B ≤
          StoppingProgram.certificateSquared C ^ (1/2:ℝ)
        """,
    PREFIX + "certificate_one_coin_guarantee": """
        ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ]
        (ρ B : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (hN : 0 < N) (C : StoppingProgram.Certificate N),
        StoppingProgram.Feasible μ ρ B C → C.bias ≤ ρ/128 →
        0 < StoppingProgram.intensity C.flow ∧
        let f := (EntropyTailLower.centeredCertificate μ C).flow
        let ν := EntropyTailLower.flowCoinSeedLaw f
        let A := EntropyTailLower.flowCoinProcedure hN f
        MeasureTheory.IsProbabilityMeasure ν ∧
          CriticalEntropy.CappedPopulationGuarantee μ ν (ObservableSimulation.gapParameter false)
            (ObservableSimulation.gapParameter true) A ρ (4*StoppingProgram.intensity C.flow*C.variance) ∧
          ∀ q, CriticalEntropy.CappedPrior μ ρ q →
            CriticalEntropy.populationExpectedWork μ ν (ObservableSimulation.gapParameter false)
              (ObservableSimulation.gapParameter true) q A ≤ ENNReal.ofReal (B/StoppingProgram.intensity C.flow)
        """,
    PREFIX + "certificate_one_coin_tradeoff": """
        ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ]
        (ρ B : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (hN : 0 < N) (C : StoppingProgram.Certificate N),
        StoppingProgram.Feasible μ ρ B C → C.bias ≤ ρ/128 →
        let f := (EntropyTailLower.centeredCertificate μ C).flow
        let ν := EntropyTailLower.flowCoinSeedLaw f
        let A := EntropyTailLower.flowCoinProcedure hN f
        (4*StoppingProgram.intensity C.flow*C.variance)*
          (CriticalEntropy.populationExpectedWork μ ν (ObservableSimulation.gapParameter false)
            (ObservableSimulation.gapParameter true) (fun _ => 0) A).toReal ≤ 4*B*C.variance
        """,
    PREFIX + "cappedGuarantee_pullback": """
        ∀ {D E R : Type} [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace R]
        (μ : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure μ]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (f : D → E), MeasurableEmbedding f → ∀ (p₀ p₁ : E → unitInterval),
        Measurable p₀ → Measurable p₁ → ∀ (A : CriticalEntropy.StoppedProcedure R ℝ) (ρ m : ℝ),
        CriticalEntropy.CappedPopulationGuarantee (μ.map f) ν p₀ p₁ A ρ m →
        CriticalEntropy.CappedPopulationGuarantee μ ν (p₀ ∘ f) (p₁ ∘ f) A ρ m
        """,
    PREFIX + "entropyGapInclusion_measurableEmbedding":
        "MeasurableEmbedding EntropyTailLower.entropyGapInclusion",
    PREFIX + "entropyGapInclusion_parameter": """
        ∀ (s : Bool), ObservableSimulation.gapParameter s ∘ EntropyTailLower.entropyGapInclusion =
          fun d => CriticalEntropy.signParameter d s
        """,
    PREFIX + "certificate_gated_annular_saturation": """
        ∀ {N : ℕ} (μ : MeasureTheory.Measure CriticalEntropy.EntropyGap) [MeasureTheory.IsProbabilityMeasure μ]
        (ρ B : ℝ), 0 < ρ → ρ ≤ 1/4 → 0 < N → ∀ (C : StoppingProgram.Certificate N),
        StoppingProgram.Feasible (μ.map EntropyTailLower.entropyGapInclusion) ρ B C → C.bias ≤ ρ/128 →
        ∀ (a : ℝ), 0 < a → a ≤ 1/4 →
        (∀ᵐ (d : CriticalEntropy.EntropyGap) ∂μ, (d:ℝ) ≤ a) →
        ∀ {K : ℕ} (I : Fin K → Set CriticalEntropy.EntropyGap) (b : Fin K → ℝ),
        (∀ i, 0 < b i) → (∀ i, MeasurableSet (I i)) →
        Pairwise (fun i j => Disjoint (I i) (I j)) →
        (∀ i d, d ∈ I i → b i/2 < (d:ℝ) ∧ (d:ℝ) ≤ b i) →
        (∀ i j, j.val = i.val+1 → 4*b j ≤ b i) →
        ∀ (s : ℝ), s ≤ 1 → (∀ i, s ≤ μ.real (I i)) →
        min (s/a^2) (ρ*EntropyTailQuantile.costEntropy (fun i => μ.real (I i)/(b i)^2)) ≤
          4294967296*Real.exp 48*B*C.variance
        """,
    PREFIX + 'certificate_localized_single_band_bound': """
        ∀ {T : Type} [Fintype T] {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap)
        [MeasureTheory.IsProbabilityMeasure μ] (ρ B : ℝ), 0 < B → 0 < N →
        ∀ C : StoppingProgram.Certificate N, StoppingProgram.Feasible μ ρ B C →
        ∀ S : T → Set Tier6.Gap, (∀ i, MeasurableSet (S i)) →
        Pairwise (fun i j => Disjoint (S i) (S j)) → (∀ i, μ (S i) ≠ 0) →
        ∀ r : T → ℝ, (∀ i, 0 < r i) → (∀ i, r i ≤ 1/4) → (∑ i, μ.real (S i)*r i) ≤ ρ →
        ∀ ν : T → MeasureTheory.Measure CriticalEntropy.EntropyGap,
        ∀ [∀ i, MeasureTheory.IsProbabilityMeasure (ν i)],
        (∀ i, (ν i).map EntropyTailLower.entropyGapInclusion = ProbabilityTheory.cond μ (S i)) →
        ∀ b : T → ℝ, (∀ i, 0 < b i) → (∀ i, b i ≤ 1/4) →
        (∀ i, ∀ᵐ (d : CriticalEntropy.EntropyGap) ∂ν i, b i/2 < (d:ℝ) ∧ (d:ℝ) ≤ b i) →
        (∑ i, μ.real (S i)*min (r i) (Real.sqrt (r i/(B*(b i)^2)))) ≤
          256*C.bias+Real.sqrt ((4294967296*Real.exp 48)*C.variance)
        """,
    PREFIX + 'certificate_disjoint_component_bias_budget': """
        ∀ {I : Type} [Fintype I] {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap)
        [MeasureTheory.IsProbabilityMeasure μ] (ρ B : ℝ) (C : StoppingProgram.Certificate N),
        StoppingProgram.Feasible μ ρ B C → ∀ (S : I → Set Tier6.Gap),
        (∀ i, MeasurableSet (S i)) → Pairwise (fun i j => Disjoint (S i) (S j)) →
        ∀ q : I → Tier6.SignLaw, (∑ i, ∫ d in S i, (q i).val d ∂μ) ≤ ρ →
        (∑ i, |∫ d in S i, (q i).val d*(StoppingProgram.biasPolynomial C).eval (d:ℝ) ∂μ|) ≤ 2*C.bias
        """,
    PREFIX + 'certificate_disjoint_component_moment_budget': """
        ∀ {I : Type} [Fintype I] {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap)
        [MeasureTheory.IsProbabilityMeasure μ] (ρ B : ℝ) (C : StoppingProgram.Certificate N),
        StoppingProgram.Feasible μ ρ B C → ∀ (S : I → Set Tier6.Gap),
        (∀ i, MeasurableSet (S i)) → Pairwise (fun i j => Disjoint (S i) (S j)) →
        ∀ q : I → Tier6.SignLaw, (∑ i, ∫ d in S i, (q i).val d ∂μ) ≤ ρ →
        (∑ i, StoppingProgram.countMean (μ.restrict (S i)) (q i) C.flow.momentWeight) ≤ C.variance
        """,
    PREFIX + 'certificate_disjoint_component_work_budget': """
        ∀ {I : Type} [Fintype I] {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap)
        [MeasureTheory.IsProbabilityMeasure μ] (ρ B : ℝ) (C : StoppingProgram.Certificate N),
        StoppingProgram.Feasible μ ρ B C → ∀ (S : I → Set Tier6.Gap),
        (∀ i, MeasurableSet (S i)) → Pairwise (fun i j => Disjoint (S i) (S j)) →
        ∀ q : I → Tier6.SignLaw, (∑ i, ∫ d in S i, (q i).val d ∂μ) ≤ ρ →
        (∑ i, StoppingProgram.countMean (μ.restrict (S i)) (q i) C.flow.continueWeight) ≤ B
        """,
    PREFIX + 'component_integral_rescale': """
        ∀ (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsFiniteMeasure μ]
        (S : Set Tier6.Gap), μ S ≠ 0 → ∀ f : Tier6.Gap → ℝ,
        μ.real S*(∫ d, f d ∂ProbabilityTheory.cond μ S) = ∫ d in S, f d ∂μ
        """,
    PREFIX + 'certificate_component_localization': """
        ∀ {I : Type} [Fintype I] {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap)
        [MeasureTheory.IsProbabilityMeasure μ] (ρ B : ℝ) (C : StoppingProgram.Certificate N),
        StoppingProgram.Feasible μ ρ B C → ∀ S : I → Set Tier6.Gap,
        (∀ i, MeasurableSet (S i)) → Pairwise (fun i j => Disjoint (S i) (S j)) →
        (∀ i, μ (S i) ≠ 0) → ∀ r : I → ℝ, (∀ i, 0 ≤ r i) →
        (∑ i, μ.real (S i)*r i) ≤ ρ →
        ∃ (D : I → StoppingProgram.Certificate N) (w : I → ℝ),
        (∀ i, (D i).flow = C.flow ∧ 0 ≤ w i ∧
          StoppingProgram.Feasible (ProbabilityTheory.cond μ (S i)) (r i) (w i) (D i)) ∧
        (∑ i, μ.real (S i)*(D i).bias) ≤ 2*C.bias ∧
        (∑ i, μ.real (S i)*(D i).variance) ≤ C.variance ∧
        (∑ i, μ.real (S i)*w i) ≤ B
        """,
    PREFIX + 'finite_component_obstructions': """
        ∀ {I : Type} [Fintype I] (u e v w r : I → ℝ) (B V b C K : ℝ),
        (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ e i) → (∀ i, 0 ≤ v i) → (∀ i, 0 ≤ w i) →
        0 < B → 0 ≤ C → 0 < K → (∑ i, e i) ≤ b → (∑ i, v i) ≤ V → (∑ i, w i) ≤ B →
        (∀ i, r i/K < e i → u i ≤ r i) →
        (∀ i, e i ≤ r i/K → (u i)^2*B ≤ C*v i*w i) →
        (∑ i, u i) ≤ K*b+Real.sqrt (C*V)
        """,
    PREFIX + 'certificate_localized_annular_bound': """
        ∀ {T : Type} [Fintype T] {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap)
        [MeasureTheory.IsProbabilityMeasure μ] (ρ B : ℝ), 0 < B → 0 < N →
        ∀ C : StoppingProgram.Certificate N, StoppingProgram.Feasible μ ρ B C →
        ∀ S : T → Set Tier6.Gap, (∀ i, MeasurableSet (S i)) →
        Pairwise (fun i j => Disjoint (S i) (S j)) → (∀ i, μ (S i) ≠ 0) →
        ∀ r : T → ℝ, (∀ i, 0 < r i) → (∀ i, r i ≤ 1/4) → (∑ i, μ.real (S i)*r i) ≤ ρ →
        ∀ ν : T → MeasureTheory.Measure CriticalEntropy.EntropyGap,
        ∀ [∀ i, MeasureTheory.IsProbabilityMeasure (ν i)],
        (∀ i, (ν i).map EntropyTailLower.entropyGapInclusion = ProbabilityTheory.cond μ (S i)) →
        ∀ a : T → ℝ, (∀ i, 0 < a i) → (∀ i, a i ≤ 1/4) →
        (∀ i, ∀ᵐ (d : CriticalEntropy.EntropyGap) ∂ν i, (d:ℝ) ≤ a i) →
        ∀ (K : T → ℕ) (J : (i : T) → Fin (K i) → Set CriticalEntropy.EntropyGap)
        (b : (i : T) → Fin (K i) → ℝ),
        (∀ i j, 0 < b i j) → (∀ i j, MeasurableSet (J i j)) →
        (∀ i, Pairwise (fun j k => Disjoint (J i j) (J i k))) →
        (∀ i j d, d ∈ J i j → b i j/2 < (d:ℝ) ∧ (d:ℝ) ≤ b i j) →
        (∀ i j k, k.val = j.val+1 → 4*b i k ≤ b i j) →
        ∀ s : T → ℝ, (∀ i, s i ≤ 1) → (∀ i j, s i ≤ (ν i).real (J i j)) →
        ∀ u : T → ℝ, (∀ i, 0 ≤ u i) → (∀ i, u i ≤ μ.real (S i)*r i) →
        (∀ i, (u i)^2*B ≤ (μ.real (S i))^2*min (s i/(a i)^2)
          (r i*EntropyTailQuantile.costEntropy (fun j => (ν i).real (J i j)/(b i j)^2))) →
        (∑ i, u i) ≤ 256*C.bias+Real.sqrt ((4294967296*Real.exp 48)*C.variance)
        """,
    PREFIX + 'certificate_canonical_band_allocation_nonneg': """
      ∀ {T : Type} [Fintype T] {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap)
      [MeasureTheory.IsProbabilityMeasure μ] (ρ B : ℝ), 0 < B → 0 < N →
      ∀ C : StoppingProgram.Certificate N, StoppingProgram.Feasible μ ρ B C →
      ∀ j : T → ℕ, Function.Injective j → (∀ i, 6 ≤ j i) →
      ∀ r : T → ℝ, (∀ i, 0 ≤ r i) → (∀ i, r i ≤ 1/4) →
      (∑ i, μ.real (EntropyTail.band (j i))*r i) ≤ ρ →
      (∑ i, μ.real (EntropyTail.band (j i))*
        min (r i) (Real.sqrt (r i/(B*((1/2:ℝ)^(j i+1))^2)))) ≤
        256*C.bias+Real.sqrt ((4294967296*Real.exp 48)*C.variance)
      """,
    PREFIX + 'smallGapLaw_map': """
      ∀ (μ : MeasureTheory.Measure Tier6.Gap),
      (∀ᵐ (d : Tier6.Gap) ∂μ, (d:ℝ) ≤ 1/128) →
      (EntropyTailLower.smallGapLaw μ).map EntropyTailLower.entropyGapInclusion = μ
      """,
    PREFIX + 'allocation_min_linear': """
      ∀ r t : ℝ, 0 ≤ r → r ≤ 1 → 0 ≤ t →
      r*min 1 t ≤ min r (t*Real.sqrt r)
      """,
    PREFIX + 'dyadic_top_mass': """
      ∀ {n : ℕ} (v : Fin n → ℝ) (s : ℝ), (∀ i, 0 ≤ v i) → 0 < s →
      (∀ i, v i ≤ s) → ∃ q : Fin n → ℝ, (∀ i, 0 ≤ q i ∧ q i ≤ 1) ∧
      (∑ i, v i*q i) ≤ s ∧
      (∑ i, v i*(2:ℝ)^(i.val+1)) ≤ 2*∑ i, v i*q i*(2:ℝ)^(i.val+1)
      """,
    PREFIX + 'sqrt_costEntropy_add': """
      ∀ {I : Type} [Fintype I] (a b : I → ℝ), (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) →
      Real.sqrt (EntropyTailQuantile.costEntropy (fun i => a i+b i)) ≤
      Real.sqrt (EntropyTailQuantile.costEntropy a)+2*Real.sqrt (EntropyTailQuantile.costEntropy b)
      """,
    PREFIX + 'binary_entropy_lower_right': """
      ∀ x y : ℝ, 0 ≤ x → 0 < y →
      y*Real.log ((x+y)/y) ≤ Real.negMulLog x+Real.negMulLog y-Real.negMulLog (x+y)
      """,
    PREFIX + 'exists_finiteSelection_minimizer': """
      ∀ {I : Type} [Fintype I] [DecidableEq I] (k : ℝ) (a e : I → ℝ),
      ∃ S : Finset I, ∀ T, EntropyTailLower.finiteSelectionScore k a e S ≤
        EntropyTailLower.finiteSelectionScore k a e T
      """,
    PREFIX + 'optimal_ordinary_band_mass': """
      ∀ {I : Type} [Fintype I] [DecidableEq I] (w b : I → ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, 0 < b i) → ∀ ρ h : ℝ, 0 ≤ ρ → 0 < h →
      ∀ S : Finset I,
      (∀ T, EntropyTailLower.finiteSelectionScore (h*Real.sqrt ρ) (fun i => w i/(b i)^2)
        (fun i => w i*min 1 (h/b i)) S ≤
        EntropyTailLower.finiteSelectionScore (h*Real.sqrt ρ) (fun i => w i/(b i)^2)
        (fun i => w i*min 1 (h/b i)) T) →
      ∀ j : I, j ∉ S → h ≤ b j → w j ≤ 4*ρ
      """,
}
SCOPE = (
    "Weighted observable sign-testing entropy (coefficient 4096), actual restart "
    "estimator reductions, arbitrary finite-law annular averaging (coefficient "
    "16384), and equivalence of the frozen statistical lower target with a "
    "uniform finite-certificate lower bound. Includes fractional priors, atomic "
    "population good gaps, population annular entropy, the observable bounded "
    "gate, its exp(+-12) stopped-word likelihood factors, and fair activation "
    "probability bounded by twice scale squared times expected gate work. "
    "Includes actual stopped-transcript measure transfer and activation/work "
    "bounds under nearby biased coins. Includes observable output masking and "
    "actual fixed-repeat averaging, preserving masked means and shrinking "
    "moments while charging every run, conditional on positive fair activation. "
    "Includes arbitrary-law population moment/work integration, an observable "
    "early-output decomposition, and signwise stopped-prefix likelihood differences. "
    "Includes the integrated early-mean bound, positive activation under a "
    "specified small scale/moment/work condition, and actual gated good gaps "
    "with exceptional mass at most 64 mZ + 4 rho. The gated moment floor absorbs "
    "this to 72 mZ. A saturated annular bound holds for arbitrary probability "
    "laws on EntropyGap supported at scale a, with coefficient 2^30 exp(48), "
    "without a small-work premise. Finite certificate centering and an actual "
    "one-coin procedure now give capped guarantees for certificate bias at "
    "most rho/128, with moment/work product at most 4 B variance. The large-bias "
    "case directly bounds selection with coefficient 1/128. Measurable parameter "
    "embeddings preserve the actual capped guarantee and connect small-gap laws "
    "to the original experiment. The resulting single-component certificate "
    "annular obstruction has coefficient 2^32 exp(48) times B variance. Disjoint "
    "component priors now give joint bias, variance, and work budgets. Attained "
    "prior optimizers construct feasible normalized component certificates with "
    "weighted bias at most twice global bias and no loss in the weighted variance "
    "and work budgets. Their localized annular costs sum to at most 256 bias plus "
    "sqrt(2^32 exp(48) variance), with explicit component, rarity-allocation, and "
    "cost premises. The single-band specialization derives finite rarity-allocation "
    "costs directly. Canonical bands with indices at least six now instantiate "
    "this bound in the original law, including zero allocations and empty bands. "
    "A fractional dyadic top-mass selection loses at most a factor of two. "
    "Finite selection minimizers exist, and ordinary bands in any such minimizer "
    "have mass at most four times rarity. These are supporting deterministic "
    "results; assembling ordinary and ignored costs, retained entropy packing, "
    "the canonical limit, and final lower bound remain obligations."
)


def scope_status(verified: bool = False) -> dict:
    return dict(valid=verified, scope=SCOPE,
                weighted_sign_entropy_verified=verified,
                annular_estimation_verified=verified,
                certificate_lower_reduction_verified=verified,
                general_population_annular_verified=verified,
                observable_activation_gate_verified=verified,
                gate_prefix_likelihood_verified=verified,
                fair_gate_probability_verified=verified,
                biased_gate_transfer_verified=verified,
                fixed_repeat_gate_bounds_verified=verified,
                population_gate_moment_work_verified=verified,
                early_output_decomposition_verified=verified,
                signwise_gate_likelihood_difference_verified=verified,
                integrated_early_output_bound_verified=verified,
                small_work_activation_positive_verified=verified,
                gated_good_gaps_verified=verified,
                gated_moment_floor_verified=verified,
                gated_annular_saturation_verified=verified,
                certificate_centering_verified=verified,
                certificate_one_coin_verified=verified,
                large_bias_certificate_lower_verified=verified,
                population_embedding_transfer_verified=verified,
                certificate_annular_obstruction_verified=verified,
                joint_component_budgets_verified=verified,
                normalized_component_certificates_verified=verified,
                localized_annular_bound_verified=verified,
                finite_single_band_allocation_verified=verified,
                canonical_band_allocations_verified=verified,
                dyadic_top_mass_verified=verified,
                entropy_increment_bound_verified=verified,
                finite_selection_ordinary_mass_verified=verified,
                full_information_gate_verified=False, gate_restart_renewal_verified=False,
                entropy_tail_lower_verified=False, entropy_tail_law_verified=False,
                closed_quantile_minimax_verified=False)


def validate_sources() -> tuple[list[Path], list[Path], set[str]]:
    freeze = json.loads(FREEZE.read_text(encoding="utf-8"))
    if (freeze["source_sha256"] != FROZEN or
            any(sha(ROOT / p) != h for p, h in FROZEN.items()) or
            freeze["target"] != PREFIX + "WeightedSignEntropyStatement" or
            freeze["coefficient"] != 4096):
        raise ValueError("Frozen weighted-sign specification changed")
    validate_dependency_freeze(SOURCE / "Specification.lean", freeze)
    validate_canonical_sources()
    validate_stopping_specification()
    paths = [module_path(PREFIX + m) for m in MODULES]
    if len(paths) != len(set(paths)) or set(paths) != set(SOURCE.rglob("*.lean")):
        raise ValueError("Missing or unregistered lower-component module")
    ordered = dependency_order(paths)
    for path in ordered:
        if FORBIDDEN.search(strip_comments(path.read_text(encoding="utf-8"))):
            raise ValueError("Forbidden proof escape in " + str(path))
    roots = [PREFIX + n for p in paths
             for n in DECLARATION.findall(strip_comments(p.read_text(encoding="utf-8")))]
    if len(roots) != len(set(roots)) or not set(EXACT_TARGETS) <= set(roots):
        raise ValueError("Duplicate or missing declaration root")
    return paths, ordered, set(roots)


def main() -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--cached-dependencies", action="store_true")
    args = parser.parse_args()
    paths, ordered, roots = validate_sources()
    rebuilt = [p for p in ordered if p in paths] if args.cached_dependencies else ordered
    protected = set(ordered) | {Path(__file__).resolve(), FREEZE,
        ROOT / "tools/verify_blind_upper_components.py", ROOT / "tools/verify_tier6.py",
        ROOT / "tools/verify_entropy_tail_components.py", ROOT / "tools/verify_entropy_tail.py",
        ROOT / "tools/entropy_tail_specification_freeze.json", ROOT / "tools/stopping_program_lock.py",
        ROOT / "tools/stopping_program_specification_freeze.json",
        LEAN / "lean-toolchain", LEAN / "lake-manifest.json", LEAN / "lakefile.toml"}
    hashes = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected)}
    cached = {}
    if args.cached_dependencies:
        for path in set(ordered) - set(rebuilt):
            obj = LEAN / ".lake/build/lib/lean" / path.relative_to(LEAN).with_suffix(".olean")
            if not obj.is_file():
                raise ValueError("Missing cached dependency: " + str(obj))
            for artifact in obj.parent.glob(obj.name + "*"):
                cached[artifact.relative_to(ROOT).as_posix()] = sha(artifact)
    output = args.output_dir or ROOT / ".runtime/entropy-tail-lower-components" / datetime.now(
        timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output.mkdir(parents=True, exist_ok=False)
    audit = LEAN / ".audit/EntropyTailLowerComponents.lean"
    source = "".join("import " + PREFIX + m + "\n" for m in MODULES) + "\n"
    source += "open ThresholdHC\nopen scoped ENNReal BigOperators\n\n"
    source += "".join(f"example : {t} := {d}\n" for d, t in EXACT_TARGETS.items())
    source += "\n" + "".join("#print axioms " + r + "\n" for r in sorted(roots))
    if FORBIDDEN.search(strip_comments(source)):
        raise ValueError("Forbidden generated audit source")
    audit.parent.mkdir(exist_ok=True)
    audit.write_text(source, encoding="utf-8")
    (output / "ExactAudit.lean").write_text(source, encoding="utf-8")
    audit_hash = sha(audit)
    status = scope_status()
    status.update(source_sha256=hashes, cached_dependency_artifact_sha256=cached,
                  audit_source_sha256=audit_hash, exact_targets=EXACT_TARGETS,
                  exact_types_checked=0, roots=sorted(roots), commands=[],
                  local_dependency_rebuild_performed=not args.cached_dependencies,
                  module_count=len(paths), rebuilt_local_modules=len(rebuilt))

    def save() -> None:
        (output / "status.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")

    save()
    commands = []
    for path in rebuilt:
        relative = path.relative_to(LEAN)
        obj = Path(".lake/build/lib/lean") / relative.with_suffix(".olean")
        (LEAN / obj).parent.mkdir(parents=True, exist_ok=True)
        commands.append([args.lake, "env", "lean", "-j", "1", "-o", str(obj), str(relative)])
    commands.append([args.lake, "env", "lean", "-j", "1", str(audit.relative_to(LEAN))])
    for i, command in enumerate(commands, 1):
        result = subprocess.run(command, cwd=LEAN, capture_output=True, text=True, encoding="utf-8")
        report = result.stdout + result.stderr
        (output / f"{i:03d}.log").write_text(report, encoding="utf-8")
        status["commands"].append(dict(command=command, exit_code=result.returncode))
        save()
        print(f"{i}/{len(commands)} {command[-1]}: exit {result.returncode}", flush=True)
        if result.returncode:
            print(report, flush=True)
            return result.returncode
    status["axioms"] = validate_reports(report, result.returncode, roots)
    validate_sources()
    if (any(sha(ROOT / p) != h for p, h in (hashes | cached).items()) or sha(audit) != audit_hash):
        raise ValueError("Protected source or reused dependency artifact changed during audit")
    status.update(scope_status(True), exact_types_checked=len(EXACT_TARGETS), declaration_count=len(roots))
    save()
    print(json.dumps(dict(valid=True, modules=len(paths), declarations=len(roots),
                          entropy_tail_lower_verified=False, evidence=str(output))), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
