
import ThresholdHC.ArbitraryLawAdaptation.CDFSelection
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.EntropyTail
open ThresholdHC.Tier6 (Gap)

example : ∀ μ : Measure ℝ, positivePart μ = μ.comap (Subtype.val : Gap → ℝ) := fun _ => rfl
example : MeasurableEmbedding (Subtype.val : Gap → ℝ) := gapEmbedding
example : ∀ σ : Measure Gap, positivePart (σ.map Subtype.val) = σ := positivePart_map
example : ∀ μ : Measure ℝ, (positivePart μ).map Subtype.val = μ.restrict (Ioc 0 (1/2)) := map_positivePart
example : ∀ σ : Measure ℝ, zeroGamma σ = if σ {0} = 0 then gamma (positivePart σ) else ∞ := fun _ => rfl
example : ∀ h d : ℝ, zeroTailWeight h d = if d ≤ 0 then 1 else ENNReal.ofReal (min 1 (h/d)) :=
  fun _ _ => rfl
example : ∀ (μ : Measure ℝ) (h : ℝ), zeroTailCost μ h = ∫⁻ d, zeroTailWeight h d ∂μ := fun _ _ => rfl
example : ∀ (μ : Measure ℝ) (ρ B : ℝ) (σ : Measure ℝ),
    zeroObjective μ ρ B σ = ENNReal.ofReal (1/Real.sqrt B)*(ENNReal.ofReal ρ*zeroGamma σ)^(1/2 : ℝ) +
      zeroTailCost (μ-σ) (1/Real.sqrt B) := fun _ _ _ _ => rfl
example : ∀ (μ : Measure ℝ) (ρ B : ℝ), zeroSelection μ ρ B =
    min (ENNReal.ofReal ρ) (⨅ (σ : Measure ℝ) (_ : σ ≤ μ), zeroObjective μ ρ B σ) := fun _ _ _ => rfl
example : ∀ {σ : Measure ℝ}, σ {0} ≠ 0 → zeroGamma σ = ∞ := @zeroGamma_of_atom
example : ∀ h : ℝ, zeroTailWeight h 0 = 1 := zeroTailWeight_zero
example : ∀ h : ℝ, Measurable (zeroTailWeight h) := measurable_zeroTailWeight
example : ∀ {h : ℝ}, 0 ≤ h → Antitone (zeroTailWeight h) := @zeroTailWeight_antitone
example : ∀ σ : Measure Gap, σ.map Subtype.val {0} = 0 := mappedGap_zero_atom
example : ∀ σ : Measure Gap, zeroGamma (σ.map Subtype.val) = gamma σ := zeroGamma_map
example : ∀ (σ : Measure Gap) (h : ℝ), zeroTailCost (σ.map Subtype.val) h = tailCost σ h := zeroTailCost_map
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] {σ : Measure Gap} (hσ : σ ≤ μ) (ρ B : ℝ),
    zeroObjective (μ.map Subtype.val) ρ B (σ.map Subtype.val) = selectionObjective μ ρ B σ := @zeroObjective_map
example {A E : Type*} [MeasurableSpace A] [MeasurableSpace E] :
    ∀ {f : A → E} (hf : MeasurableEmbedding f) {μ ν : Measure E} (h : μ ≤ ν),
    μ.comap f ≤ ν.comap f := @comap_mono_embedding A E _ _
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (ρ B : ℝ),
    zeroSelection (μ.map Subtype.val) ρ B = selection μ ρ B := @zeroSelection_map

example : ∀ z : Gap × Gap, pairGapMap z = (z.1.val, z.2.val) := fun _ => rfl
example : MeasurableEmbedding pairGapMap := pairGapEmbedding
example : ∀ (π : Measure (ℝ × ℝ))
    (hpos : ∀ᵐ z ∂π, z.1 ∈ Ioc 0 (1/2) ∧ z.2 ∈ Ioc 0 (1/2)),
    (π.comap pairGapMap).map pairGapMap = π := pairGap_comap_map
example : ∀ (π : Measure (ℝ × ℝ))
    (hpos : ∀ᵐ z ∂π, z.1 ∈ Ioc 0 (1/2) ∧ z.2 ∈ Ioc 0 (1/2)),
    (π.comap pairGapMap).map Prod.fst = positivePart (π.map Prod.fst) ∧
      (π.comap pairGapMap).map Prod.snd = positivePart (π.map Prod.snd) := pairGap_comap_marginals
example : ∀ (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hclosed : ∀ᵐ z ∂π, z.1 ∈ Icc 0 (1/2) ∧ z.2 ∈ Icc 0 (1/2))
    (hup : ∀ᵐ z ∂π, z.1 ≤ z.2),
    zeroGamma (π.map Prod.snd) ≤ 3*zeroGamma (π.map Prod.fst) := @zeroGamma_increasing_coupling
example : ∀ (π : Measure (ℝ × ℝ)) (hup : ∀ᵐ z ∂π, z.1 ≤ z.2) {h : ℝ} (hh : 0 ≤ h),
    zeroTailCost (π.map Prod.snd) h ≤ zeroTailCost (π.map Prod.fst) h := @zeroTailCost_increasing_coupling

example : ∀ (π : Measure (ℝ × ℝ)) (σ : Measure ℝ), realSelectionLift π σ =
    π.withDensity (fun z => σ.rnDeriv (π.map Prod.fst) z.1) := fun _ _ => rfl
example : ∀ (π : Measure (ℝ × ℝ)) (σ : Measure ℝ), realTransportedSelection π σ =
    (realSelectionLift π σ).map Prod.snd := fun _ _ => rfl
example : ∀ (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π] {σ : Measure ℝ} (hσ : σ ≤ π.map Prod.fst),
    (realSelectionLift π σ).map Prod.fst = σ := @realSelectionLift_first
example : ∀ (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π] {σ : Measure ℝ} (hσ : σ ≤ π.map Prod.fst),
    realSelectionLift π σ ≤ π := @realSelectionLift_le
example : ∀ (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π] {σ : Measure ℝ} (hσ : σ ≤ π.map Prod.fst),
    realTransportedSelection π σ ≤ π.map Prod.snd := @realTransportedSelection_le
example : ∀ (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π] {σ : Measure ℝ} (hσ : σ ≤ π.map Prod.fst),
    realTransportedSelection π σ Set.univ = σ Set.univ := @realTransportedSelection_mass
example : ∀ (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hclosed : ∀ᵐ z ∂π, z.1 ∈ Icc 0 (1/2) ∧ z.2 ∈ Icc 0 (1/2))
    (hup : ∀ᵐ z ∂π, z.1 ≤ z.2) {σ : Measure ℝ} (hσ : σ ≤ π.map Prod.fst) {h : ℝ} (hh : 0 ≤ h),
    zeroGamma (realTransportedSelection π σ) ≤ 3*zeroGamma σ ∧
      zeroTailCost (π.map Prod.snd-realTransportedSelection π σ) h ≤ zeroTailCost (π.map Prod.fst-σ) h :=
  @realTransportedSelection_costs
example : ∀ (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hclosed : ∀ᵐ z ∂π, z.1 ∈ Icc 0 (1/2) ∧ z.2 ∈ Icc 0 (1/2))
    (hup : ∀ᵐ z ∂π, z.1 ≤ z.2) {σ : Measure ℝ} (hσ : σ ≤ π.map Prod.fst) (ρ B : ℝ),
    zeroObjective (π.map Prod.snd) ρ B (realTransportedSelection π σ) ≤
      ENNReal.ofReal (Real.sqrt 3)*zeroObjective (π.map Prod.fst) ρ B σ := @realTransportedSelection_objective
example : ∀ (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hclosed : ∀ᵐ z ∂π, z.1 ∈ Icc 0 (1/2) ∧ z.2 ∈ Icc 0 (1/2))
    (hup : ∀ᵐ z ∂π, z.1 ≤ z.2) (ρ B : ℝ),
    zeroSelection (π.map Prod.snd) ρ B ≤ ENNReal.ofReal (Real.sqrt 3)*zeroSelection (π.map Prod.fst) ρ B :=
  @zeroSelection_increasing_coupling

example : ∀ (μ ν : Measure ℝ) (hμ : cdf μ (1/2) = 1) (hν : cdf ν (1/2) = 1),
    ∀ᵐ z ∂cdfCoupling μ ν, z.1 ∈ Icc 0 (1/2) ∧ z.2 ∈ Icc 0 (1/2) := cdfCoupling_closed_support
example : ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ0 : μ (Iio 0) = 0) (hν0 : ν (Iio 0) = 0) (hμ : cdf μ (1/2) = 1) (hν : cdf ν (1/2) = 1)
    (hdom : ∀ x, cdf ν x ≤ cdf μ x) (ρ B : ℝ),
    zeroSelection ν ρ B ≤ ENNReal.ofReal (Real.sqrt 3)*zeroSelection μ ρ B := @zeroSelection_le_sqrt_three_of_cdf
#print axioms ThresholdHC.ArbitraryLawAdaptation.cdfCoupling_closed_support
#print axioms ThresholdHC.ArbitraryLawAdaptation.comap_mono_embedding
#print axioms ThresholdHC.ArbitraryLawAdaptation.gapEmbedding
#print axioms ThresholdHC.ArbitraryLawAdaptation.map_positivePart
#print axioms ThresholdHC.ArbitraryLawAdaptation.mappedGap_zero_atom
#print axioms ThresholdHC.ArbitraryLawAdaptation.measurable_zeroTailWeight
#print axioms ThresholdHC.ArbitraryLawAdaptation.pairGapEmbedding
#print axioms ThresholdHC.ArbitraryLawAdaptation.pairGapMap
#print axioms ThresholdHC.ArbitraryLawAdaptation.pairGap_comap_map
#print axioms ThresholdHC.ArbitraryLawAdaptation.pairGap_comap_marginals
#print axioms ThresholdHC.ArbitraryLawAdaptation.positivePart
#print axioms ThresholdHC.ArbitraryLawAdaptation.positivePart_map
#print axioms ThresholdHC.ArbitraryLawAdaptation.realSelectionLift
#print axioms ThresholdHC.ArbitraryLawAdaptation.realSelectionLift_first
#print axioms ThresholdHC.ArbitraryLawAdaptation.realSelectionLift_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.realTransportedSelection
#print axioms ThresholdHC.ArbitraryLawAdaptation.realTransportedSelection_costs
#print axioms ThresholdHC.ArbitraryLawAdaptation.realTransportedSelection_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.realTransportedSelection_mass
#print axioms ThresholdHC.ArbitraryLawAdaptation.realTransportedSelection_objective
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroGamma
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroGamma_increasing_coupling
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroGamma_map
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroGamma_of_atom
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroObjective
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroObjective_map
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroSelection
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroSelection_increasing_coupling
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroSelection_le_sqrt_three_of_cdf
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroSelection_map
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroTailCost
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroTailCost_increasing_coupling
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroTailCost_map
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroTailWeight
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroTailWeight_antitone
#print axioms ThresholdHC.ArbitraryLawAdaptation.zeroTailWeight_zero
