import ThresholdHC.EntropyTailLower.Specification
import ThresholdHC.EntropyTailLower.WeightedOverlap
import ThresholdHC.EntropyTailLower.WeightedSign
import ThresholdHC.EntropyTailLower.WeightedEstimation
import ThresholdHC.EntropyTailLower.AnnularWork
import ThresholdHC.EntropyTailLower.AnnularEstimation
import ThresholdHC.EntropyTailLower.CertificateReduction
import ThresholdHC.EntropyTailLower.FractionalPrior
import ThresholdHC.EntropyTailLower.GeneralGoodGaps
import ThresholdHC.EntropyTailLower.PopulationAnnular
import ThresholdHC.EntropyTailLower.ActivationGate
import ThresholdHC.EntropyTailLower.GateLikelihood
import ThresholdHC.EntropyTailLower.FairGateWork
import ThresholdHC.EntropyTailLower.GateMeasure
import ThresholdHC.EntropyTailLower.GatedOutput
import ThresholdHC.EntropyTailLower.FiniteAverageProcedure
import ThresholdHC.EntropyTailLower.GateAverage
import ThresholdHC.EntropyTailLower.PopulationGateAverage
import ThresholdHC.EntropyTailLower.EarlyLikelihood
import ThresholdHC.EntropyTailLower.EarlyOutput
import ThresholdHC.EntropyTailLower.EarlyMean
import ThresholdHC.EntropyTailLower.GatedGoodGaps
import ThresholdHC.EntropyTailLower.GateMomentFloor
import ThresholdHC.EntropyTailLower.GatedAnnular
import ThresholdHC.EntropyTailLower.CertificateCentering
import ThresholdHC.EntropyTailLower.FlowOneCoin
import ThresholdHC.EntropyTailLower.CertificateOneCoin
import ThresholdHC.EntropyTailLower.PopulationPullback
import ThresholdHC.EntropyTailLower.CertificateAnnular
import ThresholdHC.EntropyTailLower.ComponentPriors
import ThresholdHC.EntropyTailLower.ComponentLocalization
import ThresholdHC.EntropyTailLower.LocalizationAlgebra
import ThresholdHC.EntropyTailLower.LocalizedAnnular
import ThresholdHC.EntropyTailLower.CanonicalBands
import ThresholdHC.EntropyTailLower.DyadicMass
import ThresholdHC.EntropyTailLower.EntropyIncrement
import ThresholdHC.EntropyTailLower.FiniteSelection
import ThresholdHC.EntropyTailLower.FiniteAllocation
import ThresholdHC.EntropyTailLower.CertificateLabel
import ThresholdHC.EntropyTailLower.LargeGapEntropy
import ThresholdHC.EntropyTailLower.LabelAllocation
import ThresholdHC.EntropyTailLower.GlobalCosts
import ThresholdHC.EntropyTailLower.RetainedGap
import ThresholdHC.EntropyTailLower.EntropyPacking
import ThresholdHC.EntropyTailLower.EntropyTiers
import ThresholdHC.EntropyTailLower.SeparatedGroups
import ThresholdHC.EntropyTailLower.PackedAllocation
import ThresholdHC.EntropyTailLower.CanonicalGroups
import ThresholdHC.EntropyTailLower.ComparableGroups
import ThresholdHC.EntropyTailLower.TrimmedGroup
import ThresholdHC.EntropyTailLower.JointAllocation
import ThresholdHC.EntropyTailLower.RetainedFamily
import ThresholdHC.EntropyTailLower.OptimalRetained
import ThresholdHC.EntropyTailLower.FiniteBandApprox
import ThresholdHC.EntropyTailLower.FiniteSelectionLift
import ThresholdHC.EntropyTailLower.FiniteCertificateCost
import ThresholdHC.EntropyTailLower.CertificateLower

open ThresholdHC
open scoped ENNReal BigOperators

example : ThresholdHC.EntropyTailLower.WeightedSignEntropyStatement := ThresholdHC.EntropyTailLower.weighted_sign_entropy
example : ThresholdHC.EntropyTail.EntropyTailLowerStatement ↔ (∃ c : ℝ, 0 < c ∧ ∀ (μ : MeasureTheory.Measure ThresholdHC.Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ] (ρ B : ℝ), 0 < ρ → ρ ≤ 1/4 → 0 < B → ∀ (N : ℕ), 0 < N → ∀ C : ThresholdHC.StoppingProgram.Certificate N, ThresholdHC.StoppingProgram.Feasible μ ρ B C → ENNReal.ofReal c * ThresholdHC.EntropyTail.selection μ ρ B ≤ ThresholdHC.StoppingProgram.certificateSquared C ^ (1/2 : ℝ)) := ThresholdHC.EntropyTailLower.entropy_tail_lower_iff_certificate_lower
example : 
        ∀ {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
        (μ : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure μ]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (p₀ p₁ : D → unitInterval), Measurable p₀ → Measurable p₁ →
        ∀ (ρ : unitInterval), 0 < (ρ:ℝ) → (ρ:ℝ) ≤ 1/4 →
        ∀ (m : ℝ), 2*(ρ:ℝ)/3 ≤ m → ∀ (A : CriticalEntropy.StoppedProcedure R ℝ),
        CriticalEntropy.CappedPopulationGuarantee μ ν p₀ p₁ A (ρ:ℝ) m →
        ∃ G : Set D, MeasurableSet G ∧ μ.real Gᶜ ≤ 70*m ∧
          ∀ d ∈ G, CriticalEntropy.PopulationGoodGap ν p₀ p₁ A (ρ:ℝ) m d
         := ThresholdHC.EntropyTailLower.population_good_gaps_general
example : 
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
         := ThresholdHC.EntropyTailLower.population_annular_entropy
example : 
        ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
        (A : CriticalEntropy.StoppedProcedure R E) (M H : ℕ) (z : R × (ℕ → Bool)),
        (EntropyTailLower.activationGateCost A M H z:ℕ∞) =
          min (A.stop z) (EntropyTailLower.boundaryGateCost M H z.2:ℕ∞)
         := ThresholdHC.EntropyTailLower.activationGateCost_min
example : 
        ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
        (A : CriticalEntropy.StoppedProcedure R E) (M H : ℕ) (z : R × (ℕ → Bool)),
        (EntropyTailLower.activationGate A M H).output z = true ↔
          (EntropyTailLower.boundaryGateCost M H z.2:ℕ∞) ≤ A.stop z
         := ThresholdHC.EntropyTailLower.activationGate_accepts_iff
example : 
        ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
        (A : CriticalEntropy.StoppedProcedure R E) (a d : ℝ),
        0 < a → a ≤ 1/4 → |d| ≤ a → ∀ (z : R × (ℕ → Bool)),
        let n := EntropyTailLower.activationGateCost A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ z
        let k := CriticalEntropy.wordHeads (Tier2.tapePrefix n z.2)
        Real.exp (-12) ≤ EntropyTailLower.gatePrefixLikelihood d n k ∧
          EntropyTailLower.gatePrefixLikelihood d n k ≤ Real.exp 12
         := ThresholdHC.EntropyTailLower.activationGate_prefix_likelihood
example : 
        ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (A : CriticalEntropy.StoppedProcedure R E) (M H : ℕ),
        (∫ z, (EntropyTailLower.tapeBalance (EntropyTailLower.activationGateCost A M H z) z.2:ℝ)^2
          ∂ν.prod (Tier2.tapeMeasure ⟨1/2,by norm_num⟩)) =
          ∫ z, (EntropyTailLower.activationGateCost A M H z:ℝ)
            ∂ν.prod (Tier2.tapeMeasure ⟨1/2,by norm_num⟩)
         := ThresholdHC.EntropyTailLower.activationGate_fair_square_identity
example : 
        ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (A : CriticalEntropy.StoppedProcedure R E) (a : ℝ), 0 < a →
        (ν.prod (Tier2.tapeMeasure ⟨1/2,by norm_num⟩)).real
          {z | (EntropyTailLower.activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true} ≤
          2*a^2*(CriticalEntropy.expectedStoppedProcedureWork ν ⟨1/2,by norm_num⟩
            (EntropyTailLower.activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊)).toReal
         := ThresholdHC.EntropyTailLower.activationGate_fair_scaled_probability
example : 
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
         := ThresholdHC.EntropyTailLower.activationGate_transcript_comparison
example : 
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
         := ThresholdHC.EntropyTailLower.activationGate_work_comparison
example : 
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
         := ThresholdHC.EntropyTailLower.activationGate_probability_comparison
example : 
        ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (A : CriticalEntropy.StoppedProcedure R E) (a : ℝ), 0 < a → a ≤ 1/4 →
        ∀ (p : unitInterval), |(p:ℝ)-1/2| ≤ a →
        (ν.prod (Tier2.tapeMeasure ⟨1/2,by norm_num⟩))
          {z | (EntropyTailLower.activationGate A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊).output z = true} ≤
          ENNReal.ofReal (2*Real.exp 12*a^2)*CriticalEntropy.expectedStoppedProcedureWork ν p A
         := ThresholdHC.EntropyTailLower.activationGate_fair_probability_le_biased_work
example : 
        ∀ {R : Type} [MeasurableSpace R] (A : CriticalEntropy.StoppedProcedure R ℝ) (M H : ℕ),
        (EntropyTailLower.gatedProcedure A M H).output =
          {z | (EntropyTailLower.activationGate A M H).output z = true}.indicator A.output
         := ThresholdHC.EntropyTailLower.gatedProcedure_output
example : 
        ∀ {R : Type} [MeasurableSpace R]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν] (p : unitInterval)
        (A : CriticalEntropy.StoppedProcedure R ℝ),
        CriticalEntropy.expectedStoppedProcedureWork ν p A ≠ ∞ →
        CriticalEntropy.conditionalSecondMoment ν p A ≠ ∞ → ∀ (n : ℕ),
        CriticalEntropy.conditionalMean (MeasureTheory.Measure.pi (fun _ : Fin (n+1) => ν)) p
          (EntropyTailLower.averageProcedure A n) = CriticalEntropy.conditionalMean ν p A
         := ThresholdHC.EntropyTailLower.averageProcedure_mean
example : 
        ∀ {R : Type} [MeasurableSpace R]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν] (p : unitInterval)
        (A : CriticalEntropy.StoppedProcedure R ℝ),
        CriticalEntropy.expectedStoppedProcedureWork ν p A ≠ ∞ → ∀ (M H : ℕ) (q : ℝ),
        0 < q → q ≤ 1 →
        CriticalEntropy.expectedStoppedProcedureWork
          (MeasureTheory.Measure.pi (fun _ : Fin ((EntropyTailLower.gateBatchCount q-1)+1) => ν)) p
          (EntropyTailLower.gateAverage A M H q) ≤
          ENNReal.ofReal (2/q)*CriticalEntropy.expectedStoppedProcedureWork ν p A
         := ThresholdHC.EntropyTailLower.gateAverage_work_le
example : 
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
         := ThresholdHC.EntropyTailLower.scaled_gateAverage_secondMoment_le
example : 
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
         := ThresholdHC.EntropyTailLower.population_gateAverage_uniform
example : 
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
         := ThresholdHC.EntropyTailLower.population_gateAverage_tradeoff
example : 
        ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
        (A : CriticalEntropy.StoppedProcedure R E) (a d : ℝ),
        0 < a → a ≤ 1/4 → |d| ≤ a → ∀ (z : R × (ℕ → Bool)),
        let n := EntropyTailLower.activationGateCost A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ z
        let k := CriticalEntropy.wordHeads (Tier2.tapePrefix n z.2)
        |EntropyTailLower.gatePrefixLikelihood d n k-EntropyTailLower.gatePrefixLikelihood (-d) n k| ≤
          8*Real.exp 12*|d| * |(EntropyTailLower.tapeBalance n z.2:ℝ)|
         := ThresholdHC.EntropyTailLower.activationGate_prefix_likelihood_difference
example : 
        ∀ {R : Type} [MeasurableSpace R] (A : CriticalEntropy.StoppedProcedure R ℝ) (M H : ℕ),
        (EntropyTailLower.earlyProcedure A M H).stop = (EntropyTailLower.activationGate A M H).stop
         := ThresholdHC.EntropyTailLower.earlyProcedure_stop
example : 
        ∀ {R : Type} [MeasurableSpace R]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν] (p : unitInterval)
        (A : CriticalEntropy.StoppedProcedure R ℝ),
        CriticalEntropy.conditionalSecondMoment ν p A ≠ ∞ → ∀ (M H : ℕ),
        CriticalEntropy.conditionalMean ν p (EntropyTailLower.earlyProcedure A M H)+
          CriticalEntropy.conditionalMean ν p (EntropyTailLower.gatedProcedure A M H) =
            CriticalEntropy.conditionalMean ν p A
         := ThresholdHC.EntropyTailLower.early_gated_mean_sum
example : 
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
         := ThresholdHC.EntropyTailLower.population_early_mean_difference
example : 
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
         := ThresholdHC.EntropyTailLower.fair_activation_positive_of_small_work
example : 
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
         := ThresholdHC.EntropyTailLower.population_gate_good_gaps
example : 
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
         := ThresholdHC.EntropyTailLower.population_gate_moment_floor
example : 
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
         := ThresholdHC.EntropyTailLower.population_gate_good_gaps_mass
example : 
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
         := ThresholdHC.EntropyTailLower.population_gated_annular_saturation
example : 
        ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ]
        (ρ B : ℝ), 0 ≤ ρ → ∀ (C : StoppingProgram.Certificate N),
        StoppingProgram.Feasible μ ρ B C → 0 < StoppingProgram.intensity C.flow →
        StoppingProgram.Feasible μ ρ B (EntropyTailLower.centeredCertificate μ C)
         := ThresholdHC.EntropyTailLower.centeredCertificate_feasible
example : 
        ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) (C : StoppingProgram.Certificate N),
        StoppingProgram.certificateSquared (EntropyTailLower.centeredCertificate μ C) =
          4*StoppingProgram.certificateSquared C
         := ThresholdHC.EntropyTailLower.centeredCertificate_squared
example : 
        ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ]
        (ρ B : ℝ), 0 ≤ ρ → ρ ≤ 1 → ∀ (C : StoppingProgram.Certificate N),
        StoppingProgram.Feasible μ ρ B C → ρ/2 ≤ C.bias ∨ 0 < StoppingProgram.intensity C.flow
         := ThresholdHC.EntropyTailLower.certificate_large_bias_or_positive_intensity
example : 
        ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ]
        (q : Tier6.SignLaw) (hN : 0 < N) (f : StoppingProgram.Flow N),
        StoppingProgram.FlowCone f →
        CriticalEntropy.populationMean μ (EntropyTailLower.flowCoinSeedLaw f)
          (ObservableSimulation.gapParameter false) (ObservableSimulation.gapParameter true)
          (ObservableSimulation.signUnit q) (EntropyTailLower.flowCoinProcedure hN f) =
            StoppingProgram.countMean μ q f.outputWeight
         := ThresholdHC.EntropyTailLower.flowCoinProcedure_population_mean
example : 
        ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ]
        (q : Tier6.SignLaw) (hN : 0 < N) (f : StoppingProgram.Flow N),
        StoppingProgram.FlowCone f →
        CriticalEntropy.populationSecondMoment μ (EntropyTailLower.flowCoinSeedLaw f)
          (ObservableSimulation.gapParameter false) (ObservableSimulation.gapParameter true)
          (ObservableSimulation.signUnit q) (EntropyTailLower.flowCoinProcedure hN f) ≤
            ENNReal.ofReal (StoppingProgram.intensity f*StoppingProgram.countMean μ q f.momentWeight)
         := ThresholdHC.EntropyTailLower.flowCoinProcedure_population_moment
example : 
        ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ]
        (q : Tier6.SignLaw) (hN : 0 < N) (f : StoppingProgram.Flow N),
        StoppingProgram.FlowCone f → 0 < StoppingProgram.intensity f →
        CriticalEntropy.populationExpectedWork μ (EntropyTailLower.flowCoinSeedLaw f)
          (ObservableSimulation.gapParameter false) (ObservableSimulation.gapParameter true)
          (ObservableSimulation.signUnit q) (EntropyTailLower.flowCoinProcedure hN f) =
            ENNReal.ofReal (StoppingProgram.countMean μ q f.continueWeight/StoppingProgram.intensity f)
         := ThresholdHC.EntropyTailLower.flowCoinProcedure_population_work
example : 
        ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) (ρ B : ℝ) (C : StoppingProgram.Certificate N),
        0 ≤ C.bias → 0 ≤ C.variance → ρ/128 ≤ C.bias →
        ENNReal.ofReal (1/128:ℝ)*EntropyTail.selection μ ρ B ≤
          StoppingProgram.certificateSquared C ^ (1/2:ℝ)
         := ThresholdHC.EntropyTailLower.certificate_large_bias_lower
example : 
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
         := ThresholdHC.EntropyTailLower.certificate_one_coin_guarantee
example : 
        ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ]
        (ρ B : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (hN : 0 < N) (C : StoppingProgram.Certificate N),
        StoppingProgram.Feasible μ ρ B C → C.bias ≤ ρ/128 →
        let f := (EntropyTailLower.centeredCertificate μ C).flow
        let ν := EntropyTailLower.flowCoinSeedLaw f
        let A := EntropyTailLower.flowCoinProcedure hN f
        (4*StoppingProgram.intensity C.flow*C.variance)*
          (CriticalEntropy.populationExpectedWork μ ν (ObservableSimulation.gapParameter false)
            (ObservableSimulation.gapParameter true) (fun _ => 0) A).toReal ≤ 4*B*C.variance
         := ThresholdHC.EntropyTailLower.certificate_one_coin_tradeoff
example : 
        ∀ {D E R : Type} [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace R]
        (μ : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure μ]
        (ν : MeasureTheory.Measure R) [MeasureTheory.IsProbabilityMeasure ν]
        (f : D → E), MeasurableEmbedding f → ∀ (p₀ p₁ : E → unitInterval),
        Measurable p₀ → Measurable p₁ → ∀ (A : CriticalEntropy.StoppedProcedure R ℝ) (ρ m : ℝ),
        CriticalEntropy.CappedPopulationGuarantee (μ.map f) ν p₀ p₁ A ρ m →
        CriticalEntropy.CappedPopulationGuarantee μ ν (p₀ ∘ f) (p₁ ∘ f) A ρ m
         := ThresholdHC.EntropyTailLower.cappedGuarantee_pullback
example : MeasurableEmbedding EntropyTailLower.entropyGapInclusion := ThresholdHC.EntropyTailLower.entropyGapInclusion_measurableEmbedding
example : 
        ∀ (s : Bool), ObservableSimulation.gapParameter s ∘ EntropyTailLower.entropyGapInclusion =
          fun d => CriticalEntropy.signParameter d s
         := ThresholdHC.EntropyTailLower.entropyGapInclusion_parameter
example : 
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
         := ThresholdHC.EntropyTailLower.certificate_gated_annular_saturation
example : 
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
         := ThresholdHC.EntropyTailLower.certificate_localized_single_band_bound
example : 
        ∀ {I : Type} [Fintype I] {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap)
        [MeasureTheory.IsProbabilityMeasure μ] (ρ B : ℝ) (C : StoppingProgram.Certificate N),
        StoppingProgram.Feasible μ ρ B C → ∀ (S : I → Set Tier6.Gap),
        (∀ i, MeasurableSet (S i)) → Pairwise (fun i j => Disjoint (S i) (S j)) →
        ∀ q : I → Tier6.SignLaw, (∑ i, ∫ d in S i, (q i).val d ∂μ) ≤ ρ →
        (∑ i, |∫ d in S i, (q i).val d*(StoppingProgram.biasPolynomial C).eval (d:ℝ) ∂μ|) ≤ 2*C.bias
         := ThresholdHC.EntropyTailLower.certificate_disjoint_component_bias_budget
example : 
        ∀ {I : Type} [Fintype I] {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap)
        [MeasureTheory.IsProbabilityMeasure μ] (ρ B : ℝ) (C : StoppingProgram.Certificate N),
        StoppingProgram.Feasible μ ρ B C → ∀ (S : I → Set Tier6.Gap),
        (∀ i, MeasurableSet (S i)) → Pairwise (fun i j => Disjoint (S i) (S j)) →
        ∀ q : I → Tier6.SignLaw, (∑ i, ∫ d in S i, (q i).val d ∂μ) ≤ ρ →
        (∑ i, StoppingProgram.countMean (μ.restrict (S i)) (q i) C.flow.momentWeight) ≤ C.variance
         := ThresholdHC.EntropyTailLower.certificate_disjoint_component_moment_budget
example : 
        ∀ {I : Type} [Fintype I] {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap)
        [MeasureTheory.IsProbabilityMeasure μ] (ρ B : ℝ) (C : StoppingProgram.Certificate N),
        StoppingProgram.Feasible μ ρ B C → ∀ (S : I → Set Tier6.Gap),
        (∀ i, MeasurableSet (S i)) → Pairwise (fun i j => Disjoint (S i) (S j)) →
        ∀ q : I → Tier6.SignLaw, (∑ i, ∫ d in S i, (q i).val d ∂μ) ≤ ρ →
        (∑ i, StoppingProgram.countMean (μ.restrict (S i)) (q i) C.flow.continueWeight) ≤ B
         := ThresholdHC.EntropyTailLower.certificate_disjoint_component_work_budget
example : 
        ∀ (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsFiniteMeasure μ]
        (S : Set Tier6.Gap), μ S ≠ 0 → ∀ f : Tier6.Gap → ℝ,
        μ.real S*(∫ d, f d ∂ProbabilityTheory.cond μ S) = ∫ d in S, f d ∂μ
         := ThresholdHC.EntropyTailLower.component_integral_rescale
example : 
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
         := ThresholdHC.EntropyTailLower.certificate_component_localization
example : 
        ∀ {I : Type} [Fintype I] (u e v w r : I → ℝ) (B V b C K : ℝ),
        (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ e i) → (∀ i, 0 ≤ v i) → (∀ i, 0 ≤ w i) →
        0 < B → 0 ≤ C → 0 < K → (∑ i, e i) ≤ b → (∑ i, v i) ≤ V → (∑ i, w i) ≤ B →
        (∀ i, r i/K < e i → u i ≤ r i) →
        (∀ i, e i ≤ r i/K → (u i)^2*B ≤ C*v i*w i) →
        (∑ i, u i) ≤ K*b+Real.sqrt (C*V)
         := ThresholdHC.EntropyTailLower.finite_component_obstructions
example : 
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
         := ThresholdHC.EntropyTailLower.certificate_localized_annular_bound
example : 
      ∀ {T : Type} [Fintype T] {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap)
      [MeasureTheory.IsProbabilityMeasure μ] (ρ B : ℝ), 0 < B → 0 < N →
      ∀ C : StoppingProgram.Certificate N, StoppingProgram.Feasible μ ρ B C →
      ∀ j : T → ℕ, Function.Injective j → (∀ i, 6 ≤ j i) →
      ∀ r : T → ℝ, (∀ i, 0 ≤ r i) → (∀ i, r i ≤ 1/4) →
      (∑ i, μ.real (EntropyTail.band (j i))*r i) ≤ ρ →
      (∑ i, μ.real (EntropyTail.band (j i))*
        min (r i) (Real.sqrt (r i/(B*((1/2:ℝ)^(j i+1))^2)))) ≤
        256*C.bias+Real.sqrt ((4294967296*Real.exp 48)*C.variance)
       := ThresholdHC.EntropyTailLower.certificate_canonical_band_allocation_nonneg
example : 
      ∀ (μ : MeasureTheory.Measure Tier6.Gap),
      (∀ᵐ (d : Tier6.Gap) ∂μ, (d:ℝ) ≤ 1/128) →
      (EntropyTailLower.smallGapLaw μ).map EntropyTailLower.entropyGapInclusion = μ
       := ThresholdHC.EntropyTailLower.smallGapLaw_map
example : 
      ∀ r t : ℝ, 0 ≤ r → r ≤ 1 → 0 ≤ t →
      r*min 1 t ≤ min r (t*Real.sqrt r)
       := ThresholdHC.EntropyTailLower.allocation_min_linear
example : 
      ∀ {n : ℕ} (v : Fin n → ℝ) (s : ℝ), (∀ i, 0 ≤ v i) → 0 < s →
      (∀ i, v i ≤ s) → ∃ q : Fin n → ℝ, (∀ i, 0 ≤ q i ∧ q i ≤ 1) ∧
      (∑ i, v i*q i) ≤ s ∧
      (∑ i, v i*(2:ℝ)^(i.val+1)) ≤ 2*∑ i, v i*q i*(2:ℝ)^(i.val+1)
       := ThresholdHC.EntropyTailLower.dyadic_top_mass
example : 
      ∀ {I : Type} [Fintype I] (a b : I → ℝ), (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) →
      Real.sqrt (EntropyTailQuantile.costEntropy (fun i => a i+b i)) ≤
      Real.sqrt (EntropyTailQuantile.costEntropy a)+2*Real.sqrt (EntropyTailQuantile.costEntropy b)
       := ThresholdHC.EntropyTailLower.sqrt_costEntropy_add
example : 
      ∀ x y : ℝ, 0 ≤ x → 0 < y →
      y*Real.log ((x+y)/y) ≤ Real.negMulLog x+Real.negMulLog y-Real.negMulLog (x+y)
       := ThresholdHC.EntropyTailLower.binary_entropy_lower_right
example : 
      ∀ {I : Type} [Fintype I] [DecidableEq I] (k : ℝ) (a e : I → ℝ),
      ∃ S : Finset I, ∀ T, EntropyTailLower.finiteSelectionScore k a e S ≤
        EntropyTailLower.finiteSelectionScore k a e T
       := ThresholdHC.EntropyTailLower.exists_finiteSelection_minimizer
example : 
      ∀ {I : Type} [Fintype I] [DecidableEq I] (w b : I → ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, 0 < b i) → ∀ ρ h : ℝ, 0 ≤ ρ → 0 < h →
      ∀ S : Finset I,
      (∀ T, EntropyTailLower.finiteSelectionScore (h*Real.sqrt ρ) (fun i => w i/(b i)^2)
        (fun i => w i*min 1 (h/b i)) S ≤
        EntropyTailLower.finiteSelectionScore (h*Real.sqrt ρ) (fun i => w i/(b i)^2)
        (fun i => w i*min 1 (h/b i)) T) →
      ∀ j : I, j ∉ S → h ≤ b j → w j ≤ 4*ρ
       := ThresholdHC.EntropyTailLower.optimal_ordinary_band_mass
example : 
      ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ]
      (ρ B : ℝ), 0 < ρ → ρ ≤ 1 → ∀ C : StoppingProgram.Certificate N,
      StoppingProgram.Feasible μ ρ B C → C.bias ≤ ρ/128 → ρ ≤ 16*B*C.variance
       := ThresholdHC.EntropyTailLower.certificate_small_bias_label_floor
example : 
      ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ]
      (ρ B : ℝ), 0 < ρ → ρ ≤ 1 → 0 < B → ∀ C : StoppingProgram.Certificate N,
      StoppingProgram.Feasible μ ρ B C →
      min ρ (Real.sqrt (ρ/B)) ≤ 128*C.bias+4*Real.sqrt C.variance
       := ThresholdHC.EntropyTailLower.certificate_label_floor
example : 
      ∀ w : Fin 6 → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i) ≤ 1 →
      EntropyTailQuantile.costEntropy (fun i => w i/((1/2:ℝ)^(i.val+1))^2) ≤ 16384
       := ThresholdHC.EntropyTailLower.six_band_entropy_bound
example : 
      ∀ {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ]
      (ρ B : ℝ), 0 < ρ → ρ ≤ 1 → 0 < B → ∀ C : StoppingProgram.Certificate N,
      StoppingProgram.Feasible μ ρ B C → ∀ (p : Fin 6 → Prop) [DecidablePred p],
      min ρ (Real.sqrt (ρ*EntropyTailQuantile.costEntropy (fun i : Fin 6 => if p i then
        μ.real (EntropyTail.band i.val)/((1/2:ℝ)^(i.val+1))^2 else 0)/B)) ≤
        16384*C.bias+512*Real.sqrt C.variance
       := ThresholdHC.EntropyTailLower.certificate_high_band_entropy_bound
example : 
      ∀ {T : Type} [Fintype T] {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap)
      [MeasureTheory.IsProbabilityMeasure μ] (ρ B : ℝ), 0 < B →
      ∀ C : StoppingProgram.Certificate N, StoppingProgram.Feasible μ ρ B C →
      ∀ S : T → Set Tier6.Gap, (∀ i, MeasurableSet (S i)) →
      Pairwise (fun i j => Disjoint (S i) (S j)) → (∀ i, μ (S i) ≠ 0) →
      ∀ r : T → ℝ, (∀ i, 0 < r i) → (∀ i, r i ≤ 1) →
      (∑ i, μ.real (S i)*r i) ≤ ρ → ∀ u : T → ℝ, (∀ i, 0 ≤ u i) →
      (∀ i, u i ≤ μ.real (S i)*r i) → (∀ i, (u i)^2*B ≤ (μ.real (S i))^2*r i) →
      (∑ i, u i) ≤ 256*C.bias+4*Real.sqrt C.variance
       := ThresholdHC.EntropyTailLower.certificate_localized_label_bound
example : 
      ∀ {T : Type} [Fintype T] {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap)
      [MeasureTheory.IsProbabilityMeasure μ] (ρ B : ℝ), 0 < B →
      ∀ C : StoppingProgram.Certificate N, StoppingProgram.Feasible μ ρ B C →
      ∀ j : T → ℕ, Function.Injective j → ∀ r : T → ℝ, (∀ i, 0 ≤ r i) → (∀ i, r i ≤ 1) →
      (∑ i, μ.real (EntropyTail.band (j i))*r i) ≤ ρ →
      (∑ i, μ.real (EntropyTail.band (j i))*min (r i) (Real.sqrt (r i/B))) ≤
      256*C.bias+4*Real.sqrt C.variance
       := ThresholdHC.EntropyTailLower.certificate_band_label_allocation
example : 
      ∀ {I : Type} [Fintype I] {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap)
      [MeasureTheory.IsProbabilityMeasure μ] (ρ B : ℝ), 0 < B → 0 < N →
      ∀ C : StoppingProgram.Certificate N, StoppingProgram.Feasible μ ρ B C →
      ∀ j : I → ℕ, Function.Injective j → ∀ r : I → ℝ,
      (∀ i, 0 ≤ r i) → (∀ i, r i ≤ 1/4) →
      (∑ i, μ.real (EntropyTail.band (j i))*r i) ≤ ρ →
      (∑ i, μ.real (EntropyTail.band (j i))*min (r i)
        ((1/(Real.sqrt B*((1/2:ℝ)^(j i+1))))*Real.sqrt (r i))) ≤
      65*(256*C.bias+Real.sqrt ((4294967296*Real.exp 48)*C.variance))
       := ThresholdHC.EntropyTailLower.certificate_all_band_finiteAllocationBound
example : 
      ∀ {n N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ]
      (ρ B : ℝ), 0 < ρ → 0 < B → 0 < N → ∀ C : StoppingProgram.Certificate N,
      StoppingProgram.Feasible μ ρ B C → ∀ (p : Fin n → Prop) [DecidablePred p],
      (∀ i, p i → μ.real (EntropyTail.band i.val) ≤ 4*ρ) →
      (∀ i, p i → 1/(Real.sqrt B*((1/2:ℝ)^(i.val+1))) ≤ 1) →
      (∑ i, if p i then μ.real (EntropyTail.band i.val)/(Real.sqrt B*((1/2:ℝ)^(i.val+1))) else 0) ≤
      2080*(256*C.bias+Real.sqrt ((4294967296*Real.exp 48)*C.variance))
       := ThresholdHC.EntropyTailLower.certificate_all_band_ordinary_cost
example : 
      ∀ {I : Type} [Fintype I] {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap)
      [MeasureTheory.IsProbabilityMeasure μ] (ρ B : ℝ), 0 ≤ ρ → 0 < B → 0 < N →
      ∀ C : StoppingProgram.Certificate N, StoppingProgram.Feasible μ ρ B C →
      ∀ j : I → ℕ, Function.Injective j → ∀ (p : I → Prop) [DecidablePred p],
      (∀ i, p i → 1 ≤ 1/(Real.sqrt B*((1/2:ℝ)^(j i+1)))) →
      min ρ (∑ i, if p i then μ.real (EntropyTail.band (j i)) else 0) ≤
      260*(256*C.bias+Real.sqrt ((4294967296*Real.exp 48)*C.variance))
       := ThresholdHC.EntropyTailLower.certificate_all_band_ignored_cost
example : 
      ∀ {n N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ]
      (ρ B : ℝ), 0 < ρ → 0 < B → 0 < N → ∀ C : StoppingProgram.Certificate N,
      StoppingProgram.Feasible μ ρ B C → ∀ S : Finset (Fin n),
      (∀ T, EntropyTailLower.finiteSelectionScore ((1/Real.sqrt B)*Real.sqrt ρ)
        (fun i : Fin n => μ.real (EntropyTail.band i.val)/((1/2:ℝ)^(i.val+1))^2)
        (fun i => μ.real (EntropyTail.band i.val)*min 1 ((1/Real.sqrt B)/((1/2:ℝ)^(i.val+1)))) S ≤
        EntropyTailLower.finiteSelectionScore ((1/Real.sqrt B)*Real.sqrt ρ)
        (fun i : Fin n => μ.real (EntropyTail.band i.val)/((1/2:ℝ)^(i.val+1))^2)
        (fun i => μ.real (EntropyTail.band i.val)*min 1 ((1/Real.sqrt B)/((1/2:ℝ)^(i.val+1)))) T) →
      (∑ i : Fin n, if i ∉ S ∧ 1/Real.sqrt B ≤ (1/2:ℝ)^(i.val+1) then
        μ.real (EntropyTail.band i.val)/(Real.sqrt B*((1/2:ℝ)^(i.val+1))) else 0) ≤
      2080*(256*C.bias+Real.sqrt ((4294967296*Real.exp 48)*C.variance))
       := ThresholdHC.EntropyTailLower.certificate_optimal_ordinary_cost
example : 
      ∀ {n N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsProbabilityMeasure μ]
      (ρ B : ℝ), 0 ≤ ρ → 0 < B → 0 < N → ∀ C : StoppingProgram.Certificate N,
      StoppingProgram.Feasible μ ρ B C → ∀ S : Finset (Fin n),
      min ρ (∑ i : Fin n, if i ∉ S ∧ (1/2:ℝ)^(i.val+1) < 1/Real.sqrt B then
        μ.real (EntropyTail.band i.val) else 0) ≤
      260*(256*C.bias+Real.sqrt ((4294967296*Real.exp 48)*C.variance))
       := ThresholdHC.EntropyTailLower.certificate_prefix_ignored_cost
example : 
      ∀ {I : Type} [Fintype I] [DecidableEq I] (w b : I → ℝ), (∀ i, 0 < b i) →
      ∀ (h : ℝ) (S : Finset I), (∑ i, if i ∈ S then 0 else w i*min 1 (h/b i)) =
      (∑ i, if i ∉ S ∧ h ≤ b i then w i*h/b i else 0)+
      (∑ i, if i ∉ S ∧ b i < h then w i else 0)
       := ThresholdHC.EntropyTailLower.ordinary_ignored_penalty_split
example : 
  ∀ {I : Type} [Fintype I] [DecidableEq I] (a : I → ℝ), (∀ i, 0 ≤ a i) →
  ∀ (S : Finset I) (j : I), j ∈ S → 0 < a j →
  a j*(1+Real.log (EntropyTailQuantile.costTotal (EntropyTailLower.maskedCost a S)/a j)) ≤
  EntropyTailQuantile.costEntropy (EntropyTailLower.maskedCost a S) -
    EntropyTailQuantile.costEntropy (EntropyTailLower.maskedCost a (S.erase j))
  := ThresholdHC.EntropyTailLower.costEntropy_erase_lower
example : 
  ∀ {I : Type} [Fintype I] [DecidableEq I] (w b : I → ℝ),
  (∀ i, 0 ≤ w i) → (∀ i, 0 < b i) → ∀ ρ h : ℝ, 0 ≤ ρ → 0 < h → ∀ S : Finset I,
  (∀ T, EntropyTailLower.finiteSelectionScore (h*Real.sqrt ρ) (fun i => w i/(b i)^2)
    (fun i => w i*min 1 (h/b i)) S ≤
    EntropyTailLower.finiteSelectionScore (h*Real.sqrt ρ) (fun i => w i/(b i)^2)
    (fun i => w i*min 1 (h/b i)) T) →
  ∀ j, j ∈ S → 0 < w j →
  Real.sqrt ρ*(1+Real.log (EntropyTailQuantile.costTotal
    (EntropyTailLower.maskedCost (fun i => w i/(b i)^2) S)/(w j/(b j)^2))) ≤
    2*b j*Real.sqrt (EntropyTailQuantile.costEntropy
      (EntropyTailLower.maskedCost (fun i => w i/(b i)^2) S))
  := ThresholdHC.EntropyTailLower.optimal_retained_band_gap
example : 
  ∀ {I J : Type} [Fintype I] [Fintype J] [DecidableEq J] (a : I → ℝ) (p : I → J),
  EntropyTailQuantile.costEntropy a =
    (∑ j, EntropyTailQuantile.costEntropy (fun i => if p i = j then a i else 0)) +
    EntropyTailQuantile.costEntropy (fun j => EntropyTailQuantile.costTotal
      (fun i => if p i = j then a i else 0)) - EntropyTailQuantile.costTotal a
  := ThresholdHC.EntropyTailLower.costEntropy_partition
example : 
  ∀ (n : ℕ) (a : Fin n → ℝ), (∀ i, 0 ≤ a i) →
  EntropyTailQuantile.costEntropy a ≤ EntropyTailQuantile.costTotal a +
    ∑ i, a i*(i.val+1:ℝ)*Real.log 2
  := ThresholdHC.EntropyTailLower.costEntropy_geometric_reference
example : 
  ∀ {I J : Type} [Fintype I] [Fintype J] (a : I → ℝ) (b : J → ℝ) (c : ℝ),
  0 ≤ c → (∀ i, 0 ≤ a i) → (∀ i, a i ≤ 4*c) → (∀ j, c ≤ b j) →
  0 < Fintype.card I → 0 < Fintype.card J → (Fintype.card I:ℝ)/2 ≤ Fintype.card J →
  EntropyTailQuantile.costEntropy a ≤ 64*EntropyTailQuantile.costEntropy b
  := ThresholdHC.EntropyTailLower.comparable_entropy_subfamily
example : 
  ∀ n : ℕ, 0 < n →
  0 < n - Nat.clog 4 n ∧ (n:ℝ)/2 ≤ (n - Nat.clog 4 n:ℕ)
  := ThresholdHC.EntropyTailLower.clog_four_trim_size
example : 
  ∀ (n t : ℕ) (δ : ℝ), 0 ≤ δ → ∀ b : Fin n → ℝ, (∀ i, δ ≤ b i) → n ≤ 4^t →
  (∀ (i : Fin n) (k : ℕ) (hik : i.val+k < n),
    (4:ℝ)^k*b ⟨i.val+k,hik⟩ ≤ b i) → ∀ i : Fin (n-t),
    (n:ℝ)*δ ≤ b ⟨i.val,by omega⟩
  := ThresholdHC.EntropyTailLower.trimmed_gap_amplification
example : 
  ∀ {I : Type} [Fintype I] [Nonempty I] (a : I → ℝ), (∀ i, 0 < a i) →
  ∃ (K : ℕ) (p : I → Fin K) (c : Fin K → ℝ),
  (∀ k, 0 < c k) ∧ (∀ i, c (p i) < a i ∧ a i ≤ 4*c (p i)) ∧
  EntropyTailQuantile.costEntropy a ≤
    9*∑ k, EntropyTailQuantile.costEntropy (fun i => if p i = k then a i else 0)
  := ThresholdHC.EntropyTailLower.exists_entropy_tier_partition
example : 
  ∀ {n : ℕ} (j : Fin n → ℕ), StrictMono j →
  (∀ i k, j i % 2 = j k % 2) → ∀ i k : Fin n, k.val = i.val+1 →
    4*((1/2:ℝ)^(j k+1)) ≤ (1/2:ℝ)^(j i+1)
  := ThresholdHC.EntropyTailLower.canonical_parity_separation
example : 
  ∀ S : Finset ℕ, (∀ i ∈ S, ∀ j ∈ S, i % 2 = j % 2) →
  ∀ δ : ℝ, 0 ≤ δ → (∀ j ∈ S, δ ≤ (1/2:ℝ)^(j+1)) →
  ∀ i : Fin (S.card-Nat.clog 4 S.card),
    (S.card:ℝ)*δ ≤ (1/2:ℝ)^(S.orderEmbOfFin rfl ⟨i.val,by omega⟩+1)
  := ThresholdHC.EntropyTailLower.sorted_canonical_trim_gap
example : 
  ∀ {I T : Type} [Fintype I] [Fintype T] (a : T → I → ℝ),
  (∀ t i, 0 ≤ a t i) → (∑ t, EntropyTailQuantile.costEntropy (a t)) ≤
    EntropyTailQuantile.costEntropy (fun i => ∑ t, a t i)
  := ThresholdHC.EntropyTailLower.costEntropy_sum_superadditive
example : 
  ∀ τ w a c b lam G : ℝ, 0 < a → 0 ≤ c → 0 ≤ b → 0 ≤ lam → 0 ≤ G →
  c*a^2 ≤ τ → c*b^2 ≤ w → lam*G ≤ 64*c*b →
    lam^2*G^2 ≤ 4096*(τ*w/a^2)
  := ThresholdHC.EntropyTailLower.packed_saturation_numeric
example : 
  ∀ τ w a G θ : ℝ, 0 < G → 0 ≤ w → w ≤ τ → τ/a^2 ≤ G →
  θ*G ≤ (τ*w/a^2)/4 → θ ≤ τ/4
  := ThresholdHC.EntropyTailLower.packed_rarity_cap
example : 
  ∀ θ G B : ℝ, 0 ≤ θ → 0 ≤ G → 0 < B →
  0 ≤ min θ (Real.sqrt (θ*G/B)) ∧ min θ (Real.sqrt (θ*G/B)) ≤ θ ∧
    (min θ (Real.sqrt (θ*G/B)))^2*B ≤ θ*G
  := ThresholdHC.EntropyTailLower.packed_min_cost
example : 
  ∀ {K : ℕ} (μ : MeasureTheory.Measure Tier6.Gap) [MeasureTheory.IsFiniteMeasure μ]
  (j : Fin K → ℕ), Function.Injective j →
    μ.real (⋃ i, EntropyTail.band (j i)) = ∑ i, μ.real (EntropyTail.band (j i))
  := ThresholdHC.EntropyTailLower.canonicalGroup_mass
example : 
  ∀ τ s a θ G : ℝ, 0 < τ → 0 < a →
  τ^2*min ((s/τ)/a^2) ((θ/τ)*((1/τ)*G)) = min (τ*s/a^2) (θ*G)
  := ThresholdHC.EntropyTailLower.normalized_annular_cost
example : 
  ∀ {T : Type} [Fintype T] {N : ℕ} (μ : MeasureTheory.Measure Tier6.Gap)
  [MeasureTheory.IsProbabilityMeasure μ] (ρ B : ℝ), 0 < B → 0 < N →
  ∀ C : StoppingProgram.Certificate N, StoppingProgram.Feasible μ ρ B C →
  ∀ (K : T → ℕ) (j : (i : T) → Fin (K i) → ℕ),
  (∀ i, Function.Injective (j i)) →
  (∀ i l, i ≠ l → ∀ k m, j i k ≠ j l m) →
  (∀ i, μ (⋃ k, EntropyTail.band (j i k)) ≠ 0) →
  ∀ a : T → ℝ, (∀ i, 0 < a i) → (∀ i, a i ≤ 1/128) →
  (∀ i k, (1/2:ℝ)^(j i k+1) ≤ a i) →
  (∀ i k l, l.val = k.val+1 → 4*((1/2:ℝ)^(j i l+1)) ≤ (1/2:ℝ)^(j i k+1)) →
  ∀ θ s u : T → ℝ, (∀ i, 0 < θ i) →
  (∀ i, θ i ≤ μ.real (⋃ k, EntropyTail.band (j i k))/4) → (∑ i, θ i) ≤ ρ →
  (∀ i, s i ≤ μ.real (⋃ k, EntropyTail.band (j i k))) →
  (∀ i k, s i ≤ μ.real (EntropyTail.band (j i k))) →
  (∀ i, 0 ≤ u i) → (∀ i, u i ≤ θ i) →
  (∀ i, (u i)^2*B ≤ min (μ.real (⋃ k, EntropyTail.band (j i k))*s i/(a i)^2)
    (θ i*EntropyTailQuantile.costEntropy
      (fun k => μ.real (EntropyTail.band (j i k))/((1/2:ℝ)^(j i k+1))^2))) →
  (∑ i, u i) ≤ 256*C.bias+Real.sqrt ((4294967296*Real.exp 48)*C.variance)
  := ThresholdHC.EntropyTailLower.certificate_canonical_group_bound
example : ThresholdHC.EntropyTailLower.CertificateLowerStatement := ThresholdHC.EntropyTailLower.certificate_lower
example : ∀ {N : ℕ} (μ : MeasureTheory.Measure ThresholdHC.Tier6.Gap)
    [MeasureTheory.IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1 → 0 < B → 0 < N → ∀ C : ThresholdHC.StoppingProgram.Certificate N,
    ThresholdHC.StoppingProgram.Feasible μ ρ B C →
    ThresholdHC.EntropyTail.selection μ ρ B ≤ ENNReal.ofReal
      (200000000*(256*C.bias+Real.sqrt ((4294967296*Real.exp 48)*C.variance))) := ThresholdHC.EntropyTailLower.certificate_selection_upper
example : ∀ (μ : MeasureTheory.Measure ThresholdHC.Tier6.Gap)
    [MeasureTheory.IsFiniteMeasure μ] (ρ B M : ℝ), 0 ≤ ρ →
    (∀ n : ℕ, ∃ S : Finset ℕ, (∀ j ∈ S, j < n) ∧
      min ρ (ThresholdHC.EntropyTailLower.finiteCanonicalScore μ ρ B n S) ≤ M) →
    ThresholdHC.EntropyTail.selection μ ρ B ≤ ENNReal.ofReal (2*M) := ThresholdHC.EntropyTailLower.finite_canonical_uniform_limit

#print axioms ThresholdHC.EntropyTailLower.CertificateLowerStatement
#print axioms ThresholdHC.EntropyTailLower.ComparableOrderedGroups
#print axioms ThresholdHC.EntropyTailLower.FiniteAllocationBound
#print axioms ThresholdHC.EntropyTailLower.WeightedSignEntropyStatement
#print axioms ThresholdHC.EntropyTailLower.abs_tapeBalance_le
#print axioms ThresholdHC.EntropyTailLower.activationGate
#print axioms ThresholdHC.EntropyTailLower.activationGateCost
#print axioms ThresholdHC.EntropyTailLower.activationGateCost_min
#print axioms ThresholdHC.EntropyTailLower.activationGateCost_prefix
#print axioms ThresholdHC.EntropyTailLower.activationGateValue
#print axioms ThresholdHC.EntropyTailLower.activationGate_accepts_iff
#print axioms ThresholdHC.EntropyTailLower.activationGate_bounds
#print axioms ThresholdHC.EntropyTailLower.activationGate_fair_probability_le
#print axioms ThresholdHC.EntropyTailLower.activationGate_fair_probability_le_biased_work
#print axioms ThresholdHC.EntropyTailLower.activationGate_fair_scaled_probability
#print axioms ThresholdHC.EntropyTailLower.activationGate_fair_square_identity
#print axioms ThresholdHC.EntropyTailLower.activationGate_fair_work_le_biased
#print axioms ThresholdHC.EntropyTailLower.activationGate_indicator_bound
#print axioms ThresholdHC.EntropyTailLower.activationGate_lintegral_comparison
#print axioms ThresholdHC.EntropyTailLower.activationGate_prefix_likelihood
#print axioms ThresholdHC.EntropyTailLower.activationGate_prefix_likelihood_difference
#print axioms ThresholdHC.EntropyTailLower.activationGate_probability_comparison
#print axioms ThresholdHC.EntropyTailLower.activationGate_probability_real_le
#print axioms ThresholdHC.EntropyTailLower.activationGate_rejects_stop
#print axioms ThresholdHC.EntropyTailLower.activationGate_stop_le
#print axioms ThresholdHC.EntropyTailLower.activationGate_transcript_comparison
#print axioms ThresholdHC.EntropyTailLower.activationGate_work_comparison
#print axioms ThresholdHC.EntropyTailLower.allocation_min_linear
#print axioms ThresholdHC.EntropyTailLower.annular_estimation_entropy
#print axioms ThresholdHC.EntropyTailLower.annular_sign_entropy
#print axioms ThresholdHC.EntropyTailLower.annular_work_sum
#print axioms ThresholdHC.EntropyTailLower.averageProcedure
#print axioms ThresholdHC.EntropyTailLower.averageProcedure_mean
#print axioms ThresholdHC.EntropyTailLower.averageProcedure_output_law
#print axioms ThresholdHC.EntropyTailLower.averageProcedure_secondMoment_finite
#print axioms ThresholdHC.EntropyTailLower.averageProcedure_secondMoment_le
#print axioms ThresholdHC.EntropyTailLower.averageProcedure_work
#print axioms ThresholdHC.EntropyTailLower.averaged_gate_secondMoment_le
#print axioms ThresholdHC.EntropyTailLower.balance_before_boundaryGate
#print axioms ThresholdHC.EntropyTailLower.band_subset_canonicalGroup
#print axioms ThresholdHC.EntropyTailLower.binary_entropy_le_four_sqrt
#print axioms ThresholdHC.EntropyTailLower.binary_entropy_lower_right
#print axioms ThresholdHC.EntropyTailLower.boundaryGateCost
#print axioms ThresholdHC.EntropyTailLower.bounded_fair_square_identity
#print axioms ThresholdHC.EntropyTailLower.canonicalGroup
#print axioms ThresholdHC.EntropyTailLower.canonicalGroup_cond_band_real
#print axioms ThresholdHC.EntropyTailLower.canonicalGroup_disjoint
#print axioms ThresholdHC.EntropyTailLower.canonicalGroup_mass
#print axioms ThresholdHC.EntropyTailLower.canonicalGroup_measurable
#print axioms ThresholdHC.EntropyTailLower.canonical_bandCost_upper
#print axioms ThresholdHC.EntropyTailLower.canonical_band_mass_sum_le_one
#print axioms ThresholdHC.EntropyTailLower.canonical_band_tail_upper
#print axioms ThresholdHC.EntropyTailLower.canonical_high_mask_entropy_bound
#print axioms ThresholdHC.EntropyTailLower.canonical_inverse_scale
#print axioms ThresholdHC.EntropyTailLower.canonical_parity_separation
#print axioms ThresholdHC.EntropyTailLower.canonical_prefix_remainder_tendsto_zero
#print axioms ThresholdHC.EntropyTailLower.canonical_selected_tail_upper
#print axioms ThresholdHC.EntropyTailLower.canonical_sqrt_cost_identity
#print axioms ThresholdHC.EntropyTailLower.cappedGuarantee_pullback
#print axioms ThresholdHC.EntropyTailLower.cappedPrior_event
#print axioms ThresholdHC.EntropyTailLower.cappedPrior_extend
#print axioms ThresholdHC.EntropyTailLower.capped_guarantee_bad_mean_mass
#print axioms ThresholdHC.EntropyTailLower.capped_guarantee_integrated_mean_separation
#print axioms ThresholdHC.EntropyTailLower.capped_guarantee_moment_floor_general
#print axioms ThresholdHC.EntropyTailLower.centeredCertificate
#print axioms ThresholdHC.EntropyTailLower.centeredCertificate_feasible
#print axioms ThresholdHC.EntropyTailLower.centeredCertificate_null_mean
#print axioms ThresholdHC.EntropyTailLower.centeredCertificate_squared
#print axioms ThresholdHC.EntropyTailLower.centeredFlow
#print axioms ThresholdHC.EntropyTailLower.centeredFlow_cone
#print axioms ThresholdHC.EntropyTailLower.centeredFlow_mean
#print axioms ThresholdHC.EntropyTailLower.centeredFlow_moment
#print axioms ThresholdHC.EntropyTailLower.certificate_all_band_finiteAllocationBound
#print axioms ThresholdHC.EntropyTailLower.certificate_all_band_ignored_cost
#print axioms ThresholdHC.EntropyTailLower.certificate_all_band_ordinary_cost
#print axioms ThresholdHC.EntropyTailLower.certificate_annular_bound_le_root
#print axioms ThresholdHC.EntropyTailLower.certificate_band_label_allocation
#print axioms ThresholdHC.EntropyTailLower.certificate_bias_le_root
#print axioms ThresholdHC.EntropyTailLower.certificate_bounded_entropy_cost
#print axioms ThresholdHC.EntropyTailLower.certificate_canonical_band_allocation
#print axioms ThresholdHC.EntropyTailLower.certificate_canonical_band_allocation_nonneg
#print axioms ThresholdHC.EntropyTailLower.certificate_canonical_finiteAllocationBound
#print axioms ThresholdHC.EntropyTailLower.certificate_canonical_group_bound
#print axioms ThresholdHC.EntropyTailLower.certificate_component_bias_budget
#print axioms ThresholdHC.EntropyTailLower.certificate_component_localization
#print axioms ThresholdHC.EntropyTailLower.certificate_disjoint_component_bias_budget
#print axioms ThresholdHC.EntropyTailLower.certificate_disjoint_component_moment_budget
#print axioms ThresholdHC.EntropyTailLower.certificate_disjoint_component_work_budget
#print axioms ThresholdHC.EntropyTailLower.certificate_disjoint_label_allocation
#print axioms ThresholdHC.EntropyTailLower.certificate_entropy_cap_65536
#print axioms ThresholdHC.EntropyTailLower.certificate_finite_canonical_score
#print axioms ThresholdHC.EntropyTailLower.certificate_gated_annular_saturation
#print axioms ThresholdHC.EntropyTailLower.certificate_high_band_entropy_bound
#print axioms ThresholdHC.EntropyTailLower.certificate_label_floor
#print axioms ThresholdHC.EntropyTailLower.certificate_large_bias_lower
#print axioms ThresholdHC.EntropyTailLower.certificate_large_bias_or_positive_intensity
#print axioms ThresholdHC.EntropyTailLower.certificate_localized_annular_bound
#print axioms ThresholdHC.EntropyTailLower.certificate_localized_label_bound
#print axioms ThresholdHC.EntropyTailLower.certificate_localized_single_band_bound
#print axioms ThresholdHC.EntropyTailLower.certificate_lower
#print axioms ThresholdHC.EntropyTailLower.certificate_one_coin_guarantee
#print axioms ThresholdHC.EntropyTailLower.certificate_one_coin_tradeoff
#print axioms ThresholdHC.EntropyTailLower.certificate_optimal_finite_score
#print axioms ThresholdHC.EntropyTailLower.certificate_optimal_ordinary_cost
#print axioms ThresholdHC.EntropyTailLower.certificate_optimal_retained_cost
#print axioms ThresholdHC.EntropyTailLower.certificate_prefix_ignored_cost
#print axioms ThresholdHC.EntropyTailLower.certificate_retained_family_bound
#print axioms ThresholdHC.EntropyTailLower.certificate_selection_upper
#print axioms ThresholdHC.EntropyTailLower.certificate_small_bias_label_floor
#print axioms ThresholdHC.EntropyTailLower.clog_four_le_half
#print axioms ThresholdHC.EntropyTailLower.clog_four_trim_size
#print axioms ThresholdHC.EntropyTailLower.coinTranscriptLaw
#print axioms ThresholdHC.EntropyTailLower.coinTranscriptLaw_cell
#print axioms ThresholdHC.EntropyTailLower.coinTranscriptLaw_density
#print axioms ThresholdHC.EntropyTailLower.coinTranscriptLaw_fair_density
#print axioms ThresholdHC.EntropyTailLower.coinTranscriptLaw_integral_fair
#print axioms ThresholdHC.EntropyTailLower.common_allocation_coefficient
#print axioms ThresholdHC.EntropyTailLower.comparable_cost_entropy_bounds
#print axioms ThresholdHC.EntropyTailLower.comparable_entropy_subfamily
#print axioms ThresholdHC.EntropyTailLower.comparable_entropy_trim_bound
#print axioms ThresholdHC.EntropyTailLower.comparable_group_log_bound
#print axioms ThresholdHC.EntropyTailLower.comparable_retained_gap_floor
#print axioms ThresholdHC.EntropyTailLower.comparable_retained_group_trim
#print axioms ThresholdHC.EntropyTailLower.component_certificate_optimizers
#print axioms ThresholdHC.EntropyTailLower.component_countMean_rescale
#print axioms ThresholdHC.EntropyTailLower.component_integral_rescale
#print axioms ThresholdHC.EntropyTailLower.constantPrior_countMean
#print axioms ThresholdHC.EntropyTailLower.costEntropy_add_sqrt_cross
#print axioms ThresholdHC.EntropyTailLower.costEntropy_bipartition
#print axioms ThresholdHC.EntropyTailLower.costEntropy_const
#print axioms ThresholdHC.EntropyTailLower.costEntropy_equiv
#print axioms ThresholdHC.EntropyTailLower.costEntropy_erase_difference
#print axioms ThresholdHC.EntropyTailLower.costEntropy_erase_lower
#print axioms ThresholdHC.EntropyTailLower.costEntropy_fin_prefix_le
#print axioms ThresholdHC.EntropyTailLower.costEntropy_geometric_reference
#print axioms ThresholdHC.EntropyTailLower.costEntropy_indicator_eq_subtype
#print axioms ThresholdHC.EntropyTailLower.costEntropy_orderEmb_eq_indicator
#print axioms ThresholdHC.EntropyTailLower.costEntropy_partition
#print axioms ThresholdHC.EntropyTailLower.costEntropy_partition_reference
#print axioms ThresholdHC.EntropyTailLower.costEntropy_partition_sum_le
#print axioms ThresholdHC.EntropyTailLower.costEntropy_single
#print axioms ThresholdHC.EntropyTailLower.costEntropy_sum_superadditive
#print axioms ThresholdHC.EntropyTailLower.costTotal_comp_injective_le
#print axioms ThresholdHC.EntropyTailLower.costTotal_orderEmb_eq_indicator
#print axioms ThresholdHC.EntropyTailLower.countMean_disjoint_restrictions_le
#print axioms ThresholdHC.EntropyTailLower.countMean_pasted_components_le
#print axioms ThresholdHC.EntropyTailLower.countMean_prior_maximizer
#print axioms ThresholdHC.EntropyTailLower.countMean_restrict_congr
#print axioms ThresholdHC.EntropyTailLower.dense_tier_cross
#print axioms ThresholdHC.EntropyTailLower.dyadic_top_mass
#print axioms ThresholdHC.EntropyTailLower.earlyOutput
#print axioms ThresholdHC.EntropyTailLower.earlyProcedure
#print axioms ThresholdHC.EntropyTailLower.earlyProcedure_fair_secondMoment_le
#print axioms ThresholdHC.EntropyTailLower.earlyProcedure_mean_difference_fair
#print axioms ThresholdHC.EntropyTailLower.earlyProcedure_mean_fair
#print axioms ThresholdHC.EntropyTailLower.earlyProcedure_output
#print axioms ThresholdHC.EntropyTailLower.earlyProcedure_secondMoment_le
#print axioms ThresholdHC.EntropyTailLower.earlyProcedure_stop
#print axioms ThresholdHC.EntropyTailLower.early_gated_mean_sum
#print axioms ThresholdHC.EntropyTailLower.early_gated_output_sum
#print axioms ThresholdHC.EntropyTailLower.entropyGapInclusion
#print axioms ThresholdHC.EntropyTailLower.entropyGapInclusion_measurableEmbedding
#print axioms ThresholdHC.EntropyTailLower.entropyGapInclusion_parameter
#print axioms ThresholdHC.EntropyTailLower.entropyGapInclusion_range
#print axioms ThresholdHC.EntropyTailLower.entropy_partition_tier_bound
#print axioms ThresholdHC.EntropyTailLower.entropy_tail_lower_iff_certificate_lower
#print axioms ThresholdHC.EntropyTailLower.entropy_tier_parity_refinement
#print axioms ThresholdHC.EntropyTailLower.eventPrior
#print axioms ThresholdHC.EntropyTailLower.eventPrior_integral
#print axioms ThresholdHC.EntropyTailLower.eventPrior_weighted_integral
#print axioms ThresholdHC.EntropyTailLower.exists_comparable_ordered_groups
#print axioms ThresholdHC.EntropyTailLower.exists_cost_tier
#print axioms ThresholdHC.EntropyTailLower.exists_entropy_tier_partition
#print axioms ThresholdHC.EntropyTailLower.exists_finiteSelection_minimizer
#print axioms ThresholdHC.EntropyTailLower.exists_fractional_mass
#print axioms ThresholdHC.EntropyTailLower.exists_fractional_upper_cut
#print axioms ThresholdHC.EntropyTailLower.exists_point_below_annular_average
#print axioms ThresholdHC.EntropyTailLower.exists_upper_mass_cut
#print axioms ThresholdHC.EntropyTailLower.exp_abs_sub_le
#print axioms ThresholdHC.EntropyTailLower.exp_sub_le_scaled_sub
#print axioms ThresholdHC.EntropyTailLower.expected_activationGate_work_finite
#print axioms ThresholdHC.EntropyTailLower.expected_activationGate_work_le
#print axioms ThresholdHC.EntropyTailLower.expected_activationGate_work_toReal
#print axioms ThresholdHC.EntropyTailLower.fairActivation
#print axioms ThresholdHC.EntropyTailLower.fair_activation_positive_of_small_work
#print axioms ThresholdHC.EntropyTailLower.finiteAllocationBound_dyadic_ordinary
#print axioms ThresholdHC.EntropyTailLower.finiteAllocationBound_ignored
#print axioms ThresholdHC.EntropyTailLower.finiteAllocationBound_restrict
#print axioms ThresholdHC.EntropyTailLower.finiteCanonicalScore
#print axioms ThresholdHC.EntropyTailLower.finiteSelectionScore
#print axioms ThresholdHC.EntropyTailLower.finiteSelectionScore_erase_penalty
#print axioms ThresholdHC.EntropyTailLower.finiteSelectionScore_insert_le
#print axioms ThresholdHC.EntropyTailLower.finiteSelectionScore_ordinary_penalty
#print axioms ThresholdHC.EntropyTailLower.finiteSumPrior
#print axioms ThresholdHC.EntropyTailLower.finiteSumPrior_integral
#print axioms ThresholdHC.EntropyTailLower.finiteSumPrior_rare
#print axioms ThresholdHC.EntropyTailLower.finiteSumPrior_weighted_integral
#print axioms ThresholdHC.EntropyTailLower.finite_canonical_selection_bound
#print axioms ThresholdHC.EntropyTailLower.finite_canonical_uniform_limit
#print axioms ThresholdHC.EntropyTailLower.finite_component_obstructions
#print axioms ThresholdHC.EntropyTailLower.finite_seed_integral
#print axioms ThresholdHC.EntropyTailLower.flowCoinProcedure
#print axioms ThresholdHC.EntropyTailLower.flowCoinProcedure_capped
#print axioms ThresholdHC.EntropyTailLower.flowCoinProcedure_mean
#print axioms ThresholdHC.EntropyTailLower.flowCoinProcedure_moment
#print axioms ThresholdHC.EntropyTailLower.flowCoinProcedure_output_bound
#print axioms ThresholdHC.EntropyTailLower.flowCoinProcedure_population_mean
#print axioms ThresholdHC.EntropyTailLower.flowCoinProcedure_population_moment
#print axioms ThresholdHC.EntropyTailLower.flowCoinProcedure_population_work
#print axioms ThresholdHC.EntropyTailLower.flowCoinProcedure_work_integral
#print axioms ThresholdHC.EntropyTailLower.flowCoinSeedLaw
#print axioms ThresholdHC.EntropyTailLower.flowCoinSeedLaw_probability
#print axioms ThresholdHC.EntropyTailLower.flow_countMean_square
#print axioms ThresholdHC.EntropyTailLower.gateAverage
#print axioms ThresholdHC.EntropyTailLower.gateAverage_mean_decomposition
#print axioms ThresholdHC.EntropyTailLower.gateAverage_secondMoment_le
#print axioms ThresholdHC.EntropyTailLower.gateAverage_work_le
#print axioms ThresholdHC.EntropyTailLower.gateBatchCount
#print axioms ThresholdHC.EntropyTailLower.gateBatchCount_bounds
#print axioms ThresholdHC.EntropyTailLower.gatePrefixLikelihood
#print axioms ThresholdHC.EntropyTailLower.gatePrefixLikelihood_difference
#print axioms ThresholdHC.EntropyTailLower.gatePrefixLikelihood_factor
#print axioms ThresholdHC.EntropyTailLower.gatePrefixLikelihood_log
#print axioms ThresholdHC.EntropyTailLower.gatePrefixLikelihood_log_difference
#print axioms ThresholdHC.EntropyTailLower.gatePrefixLikelihood_positive
#print axioms ThresholdHC.EntropyTailLower.gatePrefixLikelihood_ratio
#print axioms ThresholdHC.EntropyTailLower.gatePrefixLikelihood_uniform
#print axioms ThresholdHC.EntropyTailLower.gate_reference_word_likelihood
#print axioms ThresholdHC.EntropyTailLower.gate_restart_count_bounds
#print axioms ThresholdHC.EntropyTailLower.gate_scale_ceiling_bounds
#print axioms ThresholdHC.EntropyTailLower.gate_scale_reciprocal_bound
#print axioms ThresholdHC.EntropyTailLower.gatedProcedure
#print axioms ThresholdHC.EntropyTailLower.gatedProcedure_mean_square_le
#print axioms ThresholdHC.EntropyTailLower.gatedProcedure_output
#print axioms ThresholdHC.EntropyTailLower.gatedProcedure_secondMoment_le
#print axioms ThresholdHC.EntropyTailLower.gatedProcedure_work
#print axioms ThresholdHC.EntropyTailLower.gated_mean_zero_of_fair_activation_zero
#print axioms ThresholdHC.EntropyTailLower.geometric_reciprocal_sum
#print axioms ThresholdHC.EntropyTailLower.group_mass_le_scaled_entropy
#print axioms ThresholdHC.EntropyTailLower.integrable_activationGate_count
#print axioms ThresholdHC.EntropyTailLower.integrable_activationGate_square
#print axioms ThresholdHC.EntropyTailLower.integrable_survives_balance_step
#print axioms ThresholdHC.EntropyTailLower.integral_product_square_le
#print axioms ThresholdHC.EntropyTailLower.integral_survives_balance_step_fair
#print axioms ThresholdHC.EntropyTailLower.label_bound_le_annular_bound
#print axioms ThresholdHC.EntropyTailLower.log_card_half_bound
#print axioms ThresholdHC.EntropyTailLower.log_one_add_abs_le
#print axioms ThresholdHC.EntropyTailLower.log_one_add_le_two_sqrt
#print axioms ThresholdHC.EntropyTailLower.log_one_add_quadratic
#print axioms ThresholdHC.EntropyTailLower.lower_dyadic_sum
#print axioms ThresholdHC.EntropyTailLower.maskedCost
#print axioms ThresholdHC.EntropyTailLower.maskedCost_erase_add
#print axioms ThresholdHC.EntropyTailLower.maskedCost_nonneg
#print axioms ThresholdHC.EntropyTailLower.masked_mean_square_le
#print axioms ThresholdHC.EntropyTailLower.measurable_activationGateCost
#print axioms ThresholdHC.EntropyTailLower.measurable_activationGateValue
#print axioms ThresholdHC.EntropyTailLower.measurable_activationGate_balance
#print axioms ThresholdHC.EntropyTailLower.measurable_boundedFirst
#print axioms ThresholdHC.EntropyTailLower.measurable_earlyOutput
#print axioms ThresholdHC.EntropyTailLower.measurable_entropy_signParameter
#print axioms ThresholdHC.EntropyTailLower.measurable_eventPrior
#print axioms ThresholdHC.EntropyTailLower.measurable_stoppedGateLikelihood
#print axioms ThresholdHC.EntropyTailLower.measurable_stoppedReference_support
#print axioms ThresholdHC.EntropyTailLower.measurable_tapeBalance
#print axioms ThresholdHC.EntropyTailLower.measurable_transcriptOutput
#print axioms ThresholdHC.EntropyTailLower.min_add_le_min_add_min
#print axioms ThresholdHC.EntropyTailLower.mul_sqrt_ratio
#print axioms ThresholdHC.EntropyTailLower.nat_le_two_pow_pred
#print axioms ThresholdHC.EntropyTailLower.normalized_annular_cost
#print axioms ThresholdHC.EntropyTailLower.normalized_capped_entropy_cost
#print axioms ThresholdHC.EntropyTailLower.normalized_cost_entropy
#print axioms ThresholdHC.EntropyTailLower.observedPair
#print axioms ThresholdHC.EntropyTailLower.optimal_ordinary_band_mass
#print axioms ThresholdHC.EntropyTailLower.optimal_retained_band_gap
#print axioms ThresholdHC.EntropyTailLower.optimal_retained_gap
#print axioms ThresholdHC.EntropyTailLower.ordinary_ignored_penalty_split
#print axioms ThresholdHC.EntropyTailLower.ordinary_mass_of_penalty
#print axioms ThresholdHC.EntropyTailLower.packed_gap_entropy_scale
#print axioms ThresholdHC.EntropyTailLower.packed_joint_allocation
#print axioms ThresholdHC.EntropyTailLower.packed_min_cost
#print axioms ThresholdHC.EntropyTailLower.packed_rarity_cap
#print axioms ThresholdHC.EntropyTailLower.packed_saturation_numeric
#print axioms ThresholdHC.EntropyTailLower.pastedSignPrior
#print axioms ThresholdHC.EntropyTailLower.pastedSignPrior_apply
#print axioms ThresholdHC.EntropyTailLower.pastedSignPrior_rare
#print axioms ThresholdHC.EntropyTailLower.polynomial_abs_prior_maximizer
#print axioms ThresholdHC.EntropyTailLower.population_annular_entropy
#print axioms ThresholdHC.EntropyTailLower.population_annular_of_good_gaps
#print axioms ThresholdHC.EntropyTailLower.population_early_fair_secondMoment_le
#print axioms ThresholdHC.EntropyTailLower.population_early_mean_difference
#print axioms ThresholdHC.EntropyTailLower.population_eventPrior_mean
#print axioms ThresholdHC.EntropyTailLower.population_eventPrior_moment
#print axioms ThresholdHC.EntropyTailLower.population_gateAverage_bounds
#print axioms ThresholdHC.EntropyTailLower.population_gateAverage_tradeoff
#print axioms ThresholdHC.EntropyTailLower.population_gateAverage_uniform
#print axioms ThresholdHC.EntropyTailLower.population_gate_activation_bound
#print axioms ThresholdHC.EntropyTailLower.population_gate_fair_work_le
#print axioms ThresholdHC.EntropyTailLower.population_gate_good_gaps
#print axioms ThresholdHC.EntropyTailLower.population_gate_good_gaps_mass
#print axioms ThresholdHC.EntropyTailLower.population_gate_moment_floor
#print axioms ThresholdHC.EntropyTailLower.population_gated_annular_entropy
#print axioms ThresholdHC.EntropyTailLower.population_gated_annular_saturation
#print axioms ThresholdHC.EntropyTailLower.population_good_gaps_general
#print axioms ThresholdHC.EntropyTailLower.population_good_gaps_of_mean_tail
#print axioms ThresholdHC.EntropyTailLower.population_integral_map
#print axioms ThresholdHC.EntropyTailLower.population_lintegral_map
#print axioms ThresholdHC.EntropyTailLower.population_moment_floor_of_mean_gap
#print axioms ThresholdHC.EntropyTailLower.restrictedSignPrior
#print axioms ThresholdHC.EntropyTailLower.restrictedSignPrior_mean
#print axioms ThresholdHC.EntropyTailLower.restrictedSignPrior_weighted_integral
#print axioms ThresholdHC.EntropyTailLower.restrictedSignPriors_sum_le_one
#print axioms ThresholdHC.EntropyTailLower.scaled_gateAverage_secondMoment_le
#print axioms ThresholdHC.EntropyTailLower.scaled_min_bound
#print axioms ThresholdHC.EntropyTailLower.selectedCanonicalBands
#print axioms ThresholdHC.EntropyTailLower.selectedCanonicalBands_bandCost
#print axioms ThresholdHC.EntropyTailLower.selectedCanonicalBands_gamma_upper
#print axioms ThresholdHC.EntropyTailLower.selectedCanonicalBands_inter
#print axioms ThresholdHC.EntropyTailLower.selectedCanonicalBands_measurable
#print axioms ThresholdHC.EntropyTailLower.selectedCanonicalBands_tail_sum
#print axioms ThresholdHC.EntropyTailLower.separated_endpoint_power
#print axioms ThresholdHC.EntropyTailLower.separated_square_gaps
#print axioms ThresholdHC.EntropyTailLower.signTest_exponential_overlap
#print axioms ThresholdHC.EntropyTailLower.signTest_exponential_sum
#print axioms ThresholdHC.EntropyTailLower.six_band_entropy_bound
#print axioms ThresholdHC.EntropyTailLower.six_cost_entropy_bound
#print axioms ThresholdHC.EntropyTailLower.six_index_entropy_bound
#print axioms ThresholdHC.EntropyTailLower.smallGapLaw
#print axioms ThresholdHC.EntropyTailLower.smallGapLaw_map
#print axioms ThresholdHC.EntropyTailLower.smallGapLaw_probability
#print axioms ThresholdHC.EntropyTailLower.sorted_canonical_parity_separation
#print axioms ThresholdHC.EntropyTailLower.sorted_canonical_trim_gap
#print axioms ThresholdHC.EntropyTailLower.sparse_tier_mass
#print axioms ThresholdHC.EntropyTailLower.sqrt_allocation_cost
#print axioms ThresholdHC.EntropyTailLower.sqrt_costEntropy_add
#print axioms ThresholdHC.EntropyTailLower.stoppedGateLikelihood
#print axioms ThresholdHC.EntropyTailLower.stoppedGateLikelihood_eq
#print axioms ThresholdHC.EntropyTailLower.stopped_output_prefix_eq
#print axioms ThresholdHC.EntropyTailLower.stopped_sum_predictable
#print axioms ThresholdHC.EntropyTailLower.stopping_window_cost
#print axioms ThresholdHC.EntropyTailLower.sum_dyadic_powers
#print axioms ThresholdHC.EntropyTailLower.sum_half_pow_prefix
#print axioms ThresholdHC.EntropyTailLower.sum_indicator_eq_subtype
#print axioms ThresholdHC.EntropyTailLower.sum_subtype_eq_of_zero
#print axioms ThresholdHC.EntropyTailLower.sum_weighted_half_pow_le_four
#print axioms ThresholdHC.EntropyTailLower.sum_weighted_half_pow_prefix
#print axioms ThresholdHC.EntropyTailLower.survives_balance_prefix
#print axioms ThresholdHC.EntropyTailLower.tapeBalance
#print axioms ThresholdHC.EntropyTailLower.tapeBalance_heads
#print axioms ThresholdHC.EntropyTailLower.tapeBalance_prefix
#print axioms ThresholdHC.EntropyTailLower.tapeBalance_square_sum
#print axioms ThresholdHC.EntropyTailLower.tapeBalance_succ
#print axioms ThresholdHC.EntropyTailLower.tapeBalance_zero
#print axioms ThresholdHC.EntropyTailLower.tier_cross_sum
#print axioms ThresholdHC.EntropyTailLower.transcriptOutput
#print axioms ThresholdHC.EntropyTailLower.transcriptOutput_eq
#print axioms ThresholdHC.EntropyTailLower.trimmed_gap_amplification
#print axioms ThresholdHC.EntropyTailLower.upperCutPrior
#print axioms ThresholdHC.EntropyTailLower.upperCutPrior_bounds
#print axioms ThresholdHC.EntropyTailLower.upperCut_mass
#print axioms ThresholdHC.EntropyTailLower.upperMass
#print axioms ThresholdHC.EntropyTailLower.upperMass_castSucc
#print axioms ThresholdHC.EntropyTailLower.upperMass_last
#print axioms ThresholdHC.EntropyTailLower.upperMass_nonneg
#print axioms ThresholdHC.EntropyTailLower.weighted_estimation_entropy
#print axioms ThresholdHC.EntropyTailLower.weighted_order_partition
#print axioms ThresholdHC.EntropyTailLower.weighted_sign_entropy
#print axioms ThresholdHC.EntropyTailLower.weighted_upperCut_sum
#print axioms ThresholdHC.EntropyTailLower.wordLikelihood_fair_factor
