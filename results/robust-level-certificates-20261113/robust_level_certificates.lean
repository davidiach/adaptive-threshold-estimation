
import ThresholdHC.RobustContinuation.RobustLevelCertificates
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open ThresholdHC.RobustContinuation
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.BlindUpper ThresholdHC.EntropyTailUpper ThresholdHC.RareAboveTwo
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailAssembly

example : ∀ {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ] (π : Measure α) {p : α → γ} (hp : Measurable p) {g : γ → ℝ≥0∞} (hg : Measurable g),
    (π.withDensity (g ∘ p)).map p = (π.map p).withDensity g := @map_withDensity_comp
example : ∀ {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ] (π : Measure α) {p : α → γ} (hp : Measurable p) (ν₁ ν₂ : Measure γ) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] (h : π.map p = ν₁ + ν₂),
    ∃ π₁ π₂ : Measure α, π₁ + π₂ = π ∧ π₁.map p = ν₁ ∧ π₂.map p = ν₂ := @exists_split_of_map_add
example : ∀ {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ] (π : Measure α) {p : α → γ} (hp : Measurable p) (ν₁ ν₂ ν₃ : Measure γ) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] [IsFiniteMeasure ν₃] (h : π.map p = ν₁ + ν₂ + ν₃),
    ∃ π₁ π₂ π₃ : Measure α, π₁ + π₂ + π₃ = π ∧ π₁.map p = ν₁ ∧ π₂.map p = ν₂ ∧
      π₃.map p = ν₃ := @exists_split_of_map_add₃
example : ∀ (σ τ ζ : Measure Gap) (a : ℝ≥0∞) (d : Gap),
    threePieceEnvelope (a • σ) (a • τ) (a • ζ) d = a.toReal * threePieceEnvelope σ τ ζ d := @threePieceEnvelope_smul
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η) (hσ : Integrable (fun x : Gap => (x:ℝ)⁻¹^2) σ) (hτ : Integrable (fun x : Gap => (x:ℝ)⁻¹) τ) (weights : ℕ → ℝ≥0) {ε ρ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ) (j L : ℕ) (hw : 0 < (weights j:ℝ)) (hw1 : (weights j:ℝ) ≤ 1) {d₀ d : Gap} (hd : d₀ ∈ band j) (h : (d₀:ℝ) ≤ d),
    conditionalRaceWork (negativeBankTest weights ε) (positiveBankTest η weights (ρ*ε/c))
      L true d ≤
      12*positiveAllowance ε (weights j:ℝ) ρ (threePieceEnvelope σ τ ζ d₀)/(d₀:ℝ)^2 := @scaled_bank_positive_work
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η) (hσ : Integrable (fun x : Gap => (x:ℝ)⁻¹^2) σ) (hτ : Integrable (fun x : Gap => (x:ℝ)⁻¹) τ) (weights : ℕ → ℝ≥0) {ε ρ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ) (j L : ℕ) (hw : 0 < (weights j:ℝ)) (hw1 : (weights j:ℝ) ≤ 1) (q : SignLaw) {d₀ d : Gap} (hd : d₀ ∈ band j) (h : (d₀:ℝ) ≤ d),
    mixtureRaceWork q (negativeBankTest weights ε) (positiveBankTest η weights (ρ*ε/c)) L d ≤
      12*(d₀:ℝ)⁻¹^2*(1+Real.log (ε⁻¹)+Real.log ((weights j:ℝ)⁻¹))+
      12*q.val d*(d₀:ℝ)⁻¹^2*logPlus (threePieceEnvelope σ τ ζ d₀/ρ) := @scaled_bank_mixture_work
example : ∀ (π : Measure (Gap × Gap)) {σ : Measure Gap} (hfst : π.map Prod.fst = σ) {t : ℝ} {N : ℕ} (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (f : Gap × Gap → ℝ) (hf : ∀ j : Fin N, IntegrableOn f (Prod.fst ⁻¹' band j.val) π),
    (∫ z, f z ∂π) = ∑ j : Fin N, ∫ z in Prod.fst ⁻¹' band j.val, f z ∂π := @coupled_integral_eq_sum_bands
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (q : SignLaw) (neg pos : PrefixTest) (L : ℕ),
    Integrable (fun z : Gap × Gap => mixtureRaceWork q neg pos L z.2) π := @integrable_coupledRaceWork
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η) (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (hfst : π.map Prod.fst = σ) {t ε ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hA : 0 < ∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ) (hz : ζ.real univ ≤ ρ) (q : SignLaw) (hq : (∫ z, q.val z.2 ∂π) ≤ ρ) (L : ℕ),
    (∫ z, mixtureRaceWork q (negativeBankTest (bandWeights σ) ε)
      (positiveBankTest η (bandWeights σ) (ρ*ε/c)) L z.2 ∂π) ≤
      12*costEntropy (fun j : Fin N => bandCost σ j.val) +
      12*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ)*Real.log (ε⁻¹) +
      12*(Real.log 3+1)*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) +
      6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ := @coupled_selected_work
example : ∀ (π : Measure (Gap × Gap)) (h : π.map Prod.fst = 0),
    π = 0 := @coupling_eq_zero_of_fst
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η) (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (hfst : π.map Prod.fst = σ) {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hz : ζ.real univ ≤ ρ) (q : SignLaw) (hq : (∫ z, q.val z.2 ∂π) ≤ ρ) (l L : ℕ),
    (∫ z, mixtureRaceWork q (negativeBankTest (referenceWeights σ) (levelEpsilon l))
      (positiveBankTest η (referenceWeights σ) (ρ*levelEpsilon l/c)) L z.2 ∂π) ≤
      128*(l+1)*costEntropy (fun j : Fin N => bandCost σ j.val) +
      6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ := @coupled_selected_level_work
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (τ : Measure Gap) [IsFiniteMeasure τ] (hfst : π.map Prod.fst = τ) (q : SignLaw) (neg pos : PrefixTest) (L : ℕ),
    (∫ z, mixtureRaceWork q neg pos L z.2 ∂π) ≤ 2*ordinaryCost τ (Uniform713.cap L) := @coupled_work_le_ordinary
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (q : SignLaw) (neg pos : PrefixTest) (L : ℕ),
    (∫ z, mixtureRaceWork q neg pos L z.2 ∂π) ≤ 2*Uniform713.cap L*π.real univ := @coupled_work_le_cap
example : ∀ (π : Measure (Gap × Gap)) {ν : Measure Gap} (hfst : π.map Prod.fst = ν),
    π.real univ = ν.real univ := @coupling_real_univ
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η) (πσ πτ πζ : Measure (Gap × Gap)) [IsFiniteMeasure πσ] [IsFiniteMeasure πτ] [IsFiniteMeasure πζ] (hupσ : ∀ᵐ z ∂πσ, (z.1:ℝ) ≤ z.2) (hupτ : ∀ᵐ z ∂πτ, (z.1:ℝ) ≤ z.2) (hfσ : πσ.map Prod.fst = σ) (hfτ : πτ.map Prod.fst = τ) (hfζ : πζ.map Prod.fst = ζ) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hz : ζ.real univ ≤ ρ) (q : SignLaw) (hq : RarePrior (πσ.map Prod.snd + πτ.map Prod.snd + πζ.map Prod.snd + μ₀) ρ q) (l L : ℕ),
    (∫ d, mixtureRaceWork q (negativeBankTest (referenceWeights σ) (levelEpsilon l))
      (positiveBankTest η (referenceWeights σ) (ρ*levelEpsilon l/c)) L d
      ∂(πσ.map Prod.snd + πτ.map Prod.snd + πζ.map Prod.snd + μ₀)) ≤
      128*(l+1)*costEntropy (fun j : Fin N => bandCost σ j.val) +
      6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ + 2*ordinaryCost τ (Uniform713.cap L) +
      2*Uniform713.cap L*(ζ.real univ + μ₀.real univ) := @coupled_three_piece_level_work
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η) (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hz : ζ.real univ ≤ ρ) (q : SignLaw) (hq : RarePrior (π.map Prod.snd + μ₀) ρ q) (l L : ℕ),
    (∫ d, mixtureRaceWork q (negativeBankTest (referenceWeights σ) (levelEpsilon l))
      (positiveBankTest η (referenceWeights σ) (ρ*levelEpsilon l/c)) L d
      ∂(π.map Prod.snd + μ₀)) ≤
      128*(l+1)*costEntropy (fun j : Fin N => bandCost σ j.val) +
      6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ + 2*ordinaryCost τ (Uniform713.cap L) +
      2*Uniform713.cap L*(ζ.real univ + μ₀.real univ) := @robust_three_piece_level_work
example : ∀ (η : Measure Gap) {c : ℝ} (hc : 0 ≤ c) (M : ℝ),
    eta (ENNReal.ofReal c • η) M = c * eta η M := @eta_smul_ofReal
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (ν ζ : Measure Gap) [IsFiniteMeasure ν] [IsFiniteMeasure ζ] {c : ℝ} (hc : 0 < c) (hdesign : ν+ζ = ENNReal.ofReal c • η) (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] (weights : ℕ → ℝ≥0) (hw : HasSum weights 1) {ρ : ℝ} (hρ : 0 < ρ) (q : SignLaw) (hq : RarePrior (π.map Prod.snd + μ₀) ρ q) (l k : ℕ) (hk : eta ν (4 ^ k) ≤ levelAccuracy ρ l/8) (hz : ζ.real univ + μ₀.real univ ≤ levelAccuracy ρ l/8),
    racePopulationError (π.map Prod.snd + μ₀) q (negativeBankTest weights (levelEpsilon l))
      (positiveBankTest η weights (ρ*levelEpsilon l/c)) (2*k) ≤ levelAccuracy ρ l := @robust_level_error
#print axioms ThresholdHC.RobustContinuation.coupled_integral_eq_sum_bands
#print axioms ThresholdHC.RobustContinuation.coupled_selected_level_work
#print axioms ThresholdHC.RobustContinuation.coupled_selected_work
#print axioms ThresholdHC.RobustContinuation.coupled_three_piece_level_work
#print axioms ThresholdHC.RobustContinuation.coupled_work_le_cap
#print axioms ThresholdHC.RobustContinuation.coupled_work_le_ordinary
#print axioms ThresholdHC.RobustContinuation.coupling_eq_zero_of_fst
#print axioms ThresholdHC.RobustContinuation.coupling_real_univ
#print axioms ThresholdHC.RobustContinuation.eta_smul_ofReal
#print axioms ThresholdHC.RobustContinuation.exists_split_of_map_add
#print axioms ThresholdHC.RobustContinuation.exists_split_of_map_add₃
#print axioms ThresholdHC.RobustContinuation.integrable_coupledRaceWork
#print axioms ThresholdHC.RobustContinuation.map_withDensity_comp
#print axioms ThresholdHC.RobustContinuation.robust_level_error
#print axioms ThresholdHC.RobustContinuation.robust_three_piece_level_work
#print axioms ThresholdHC.RobustContinuation.scaled_bank_mixture_work
#print axioms ThresholdHC.RobustContinuation.scaled_bank_positive_work
#print axioms ThresholdHC.RobustContinuation.threePieceEnvelope_smul
