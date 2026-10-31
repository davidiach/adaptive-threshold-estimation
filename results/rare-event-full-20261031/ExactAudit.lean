import ThresholdHC.CapIdentification.AffineCentering
import ThresholdHC.CapIdentification.AffineRecovery
import ThresholdHC.CapIdentification.BiasApproximation
import ThresholdHC.CapIdentification.BiasFloor
import ThresholdHC.CapIdentification.BudgetLimit
import ThresholdHC.CapIdentification.CenteredBasis
import ThresholdHC.CapIdentification.ContrastFunctional
import ThresholdHC.CapIdentification.CountBounds
import ThresholdHC.CapIdentification.CountMatching
import ThresholdHC.CapIdentification.DiameterAttainment
import ThresholdHC.CapIdentification.DiameterConsequences
import ThresholdHC.CapIdentification.FiniteSeparation
import ThresholdHC.CapIdentification.FiniteSupportTarget
import ThresholdHC.CapIdentification.Full
import ThresholdHC.CapIdentification.FullCapCertificate
import ThresholdHC.CapIdentification.InformationZero
import ThresholdHC.CapIdentification.Interpolation
import ThresholdHC.CapIdentification.MomentCoordinates
import ThresholdHC.CapIdentification.OddPolynomials
import ThresholdHC.CapIdentification.OrthogonalContrast
import ThresholdHC.CapIdentification.PolynomialL2
import ThresholdHC.CapIdentification.PrefixBasis
import ThresholdHC.CapIdentification.PrefixRepresentation
import ThresholdHC.CapIdentification.RareContrast
import ThresholdHC.CapIdentification.StoppedMatching
import ThresholdHC.CapIdentification.SupportIdentification
import ThresholdHC.CapIdentification.TerminalMoments
import ThresholdHC.EntropyTail.Band
import ThresholdHC.EntropyTail.Bounds
import ThresholdHC.EntropyTail.Entropy
import ThresholdHC.EntropyTail.Gamma
import ThresholdHC.EntropyTail.HardSelection
import ThresholdHC.EntropyTail.Model
import ThresholdHC.EntropyTail.Nonvacuity
import ThresholdHC.EntropyTail.Objective
import ThresholdHC.EntropyTail.SingleAtom
import ThresholdHC.EntropyTail.Specification
import ThresholdHC.EntropyTail.Superadditive
import ThresholdHC.EntropyTailAssembly.AccuracySchedule
import ThresholdHC.EntropyTailAssembly.BandEntropy
import ThresholdHC.EntropyTailAssembly.BandWeights
import ThresholdHC.EntropyTailAssembly.BudgetCertificate
import ThresholdHC.EntropyTailAssembly.CertificateAlgebra
import ThresholdHC.EntropyTailAssembly.ConditionalWork
import ThresholdHC.EntropyTailAssembly.DyadicKernelPointwise
import ThresholdHC.EntropyTailAssembly.DyadicKernelSum
import ThresholdHC.EntropyTailAssembly.ErrorCaps
import ThresholdHC.EntropyTailAssembly.FiniteApproximation
import ThresholdHC.EntropyTailAssembly.IntegratedSurcharge
import ThresholdHC.EntropyTailAssembly.KernelMoments
import ThresholdHC.EntropyTailAssembly.LevelCertificates
import ThresholdHC.EntropyTailAssembly.MixedWork
import ThresholdHC.EntropyTailAssembly.OrdinaryKernels
import ThresholdHC.EntropyTailAssembly.SelectedWork
import ThresholdHC.EntropyTailAssembly.UnresolvedWork
import ThresholdHC.EntropyTailBridge.Compatibility
import ThresholdHC.EntropyTailBridge.Upper
import ThresholdHC.EntropyTailExecution.ActualPlan
import ThresholdHC.EntropyTailExecution.AllocatedEstimator
import ThresholdHC.EntropyTailExecution.CallMachine
import ThresholdHC.EntropyTailExecution.CoupledCall
import ThresholdHC.EntropyTailExecution.EntropyLimit
import ThresholdHC.EntropyTailExecution.FiniteRisk
import ThresholdHC.EntropyTailExecution.IncrementBounds
import ThresholdHC.EntropyTailExecution.PlanExecution
import ThresholdHC.EntropyTailExecution.PoissonPlan
import ThresholdHC.EntropyTailExecution.RealizedPoisson
import ThresholdHC.EntropyTailExecution.ScheduledFamily
import ThresholdHC.EntropyTailExecution.ThreePiece
import ThresholdHC.EntropyTailExecution.UpperTheorem
import ThresholdHC.EntropyTailQuantile.BandGeometry
import ThresholdHC.EntropyTailQuantile.CostEntropy
import ThresholdHC.EntropyTailQuantile.CostEntropySeries
import ThresholdHC.EntropyTailQuantile.CutDecomposition
import ThresholdHC.EntropyTailQuantile.EntropyMixture
import ThresholdHC.EntropyTailQuantile.EntropyMoment
import ThresholdHC.EntropyTailQuantile.MeasureEntropy
import ThresholdHC.EntropyTailQuantile.Model
import ThresholdHC.EntropyTailQuantile.QuantileAlgebra
import ThresholdHC.EntropyTailQuantile.QuantileComparison
import ThresholdHC.EntropyTailQuantile.QuantileCoreBound
import ThresholdHC.EntropyTailQuantile.QuantileFeasible
import ThresholdHC.EntropyTailQuantile.QuantileRootBound
import ThresholdHC.EntropyTailQuantile.QuantileSplit
import ThresholdHC.EntropyTailQuantile.QuantileSplitFull
import ThresholdHC.EntropyTailQuantile.QuantileTailBound
import ThresholdHC.EntropyTailQuantile.QuantileThreshold
import ThresholdHC.EntropyTailQuantile.ScaleSeparated
import ThresholdHC.EntropyTailQuantile.Specification
import ThresholdHC.EntropyTailQuantile.TailModulus
import ThresholdHC.EntropyTailSampling.CountedMarks
import ThresholdHC.EntropyTailSampling.MultilevelPoisson
import ThresholdHC.EntropyTailSampling.PoissonEstimator
import ThresholdHC.EntropyTailSampling.PositiveRace
import ThresholdHC.EntropyTailSampling.RaceMoments
import ThresholdHC.EntropyTailUpper.Allocation
import ThresholdHC.EntropyTailUpper.BankErrors
import ThresholdHC.EntropyTailUpper.BankRace
import ThresholdHC.EntropyTailUpper.BankWork
import ThresholdHC.EntropyTailUpper.BernoulliTilt
import ThresholdHC.EntropyTailUpper.BoundedSearch
import ThresholdHC.EntropyTailUpper.LaplaceEnvelope
import ThresholdHC.EntropyTailUpper.LogSurcharge
import ThresholdHC.EntropyTailUpper.NullMixture
import ThresholdHC.EntropyTailUpper.NullPrefix
import ThresholdHC.EntropyTailUpper.Ordinary
import ThresholdHC.EntropyTailUpper.ParityRace
import ThresholdHC.EntropyTailUpper.PoissonMoments
import ThresholdHC.EntropyTailUpper.PopulationErrors
import ThresholdHC.EntropyTailUpper.PositiveRaceWork
import ThresholdHC.EntropyTailUpper.PredictableWald
import ThresholdHC.EntropyTailUpper.PrefixConcentration
import ThresholdHC.EntropyTailUpper.PrefixCrossing
import ThresholdHC.EntropyTailUpper.ReferenceDrift
import ThresholdHC.EntropyTailUpper.ReferenceLikelihood
import ThresholdHC.EntropyTailUpper.ScoreHitting
import ThresholdHC.EntropyTailUpper.SurvivalWork
import ThresholdHC.Genie.AtomConicModel
import ThresholdHC.Genie.AtomConicRealization
import ThresholdHC.Genie.BellmanEnvelope
import ThresholdHC.Genie.CapLimits
import ThresholdHC.Genie.CapMonotonicity
import ThresholdHC.Genie.CompactDecreasingMaximum
import ThresholdHC.Genie.CompactPriorDomain
import ThresholdHC.Genie.DirectRisk
import ThresholdHC.Genie.DirectRiskOptimization
import ThresholdHC.Genie.DualTopology
import ThresholdHC.Genie.ExtendedFlowConservation
import ThresholdHC.Genie.FiniteConicEnvelope
import ThresholdHC.Genie.FiniteConicPrice
import ThresholdHC.Genie.FiniteConicValue
import ThresholdHC.Genie.FinitePosterior
import ThresholdHC.Genie.FinitePriors
import ThresholdHC.Genie.FiniteReveal
import ThresholdHC.Genie.FlowDepth
import ThresholdHC.Genie.FlowExtension
import ThresholdHC.Genie.FlowTruncation
import ThresholdHC.Genie.InfiniteComparison
import ThresholdHC.Genie.InfiniteCoordinates
import ThresholdHC.Genie.InfiniteDivergence
import ThresholdHC.Genie.InfiniteDivergenceExample
import ThresholdHC.Genie.InfiniteDualLimit
import ThresholdHC.Genie.InfiniteDuality
import ThresholdHC.Genie.InfiniteMidpoint
import ThresholdHC.Genie.InformationTopology
import ThresholdHC.Genie.LatentModel
import ThresholdHC.Genie.LatentMoments
import ThresholdHC.Genie.LatentPrefix
import ThresholdHC.Genie.LatentScore
import ThresholdHC.Genie.LatentTape
import ThresholdHC.Genie.Model
import ThresholdHC.Genie.ObservationFiltration
import ThresholdHC.Genie.OptimizedBrackets
import ThresholdHC.Genie.OptimizedConvergence
import ThresholdHC.Genie.PerspectiveIntegral
import ThresholdHC.Genie.PerspectiveTopology
import ThresholdHC.Genie.ReferenceRegularization
import ThresholdHC.Genie.RevealBellman
import ThresholdHC.Genie.RevealConvergence
import ThresholdHC.Genie.RevealFiniteness
import ThresholdHC.Genie.RevealProgram
import ThresholdHC.Genie.RevealResidual
import ThresholdHC.Genie.RevealReward
import ThresholdHC.Genie.RevealTruncation
import ThresholdHC.Genie.ScalarPrice
import ThresholdHC.Genie.SingularFlowBound
import ThresholdHC.Genie.SingularPrefixBound
import ThresholdHC.Genie.TapeIdentification
import ThresholdHC.Genie.UniformGapModel
import ThresholdHC.Genie.UniformMoments
import ThresholdHC.Genie.UniformPrefixes
import ThresholdHC.StoppingProgram.AbsorbedPriors
import ThresholdHC.StoppingProgram.AbsorptionRatio
import ThresholdHC.StoppingProgram.AffinityOverlap
import ThresholdHC.StoppingProgram.AffinityRisk
import ThresholdHC.StoppingProgram.Bellman
import ThresholdHC.StoppingProgram.BellmanFlow
import ThresholdHC.StoppingProgram.BellmanTheorem
import ThresholdHC.StoppingProgram.BernoulliFloor
import ThresholdHC.StoppingProgram.CertificateCap
import ThresholdHC.StoppingProgram.CertificateRealization
import ThresholdHC.StoppingProgram.ClosedProgram
import ThresholdHC.StoppingProgram.CompactMaximum
import ThresholdHC.StoppingProgram.ConeLagrange
import ThresholdHC.StoppingProgram.ConePriceRatio
import ThresholdHC.StoppingProgram.ConstantInformation
import ThresholdHC.StoppingProgram.ContractionScale
import ThresholdHC.StoppingProgram.CreationInformation
import ThresholdHC.StoppingProgram.DecisionIndependence
import ThresholdHC.StoppingProgram.DecisionMixture
import ThresholdHC.StoppingProgram.DualTheorem
import ThresholdHC.StoppingProgram.FiniteCertificate
import ThresholdHC.StoppingProgram.FinitePopulationInformation
import ThresholdHC.StoppingProgram.FiniteProgram
import ThresholdHC.StoppingProgram.FlowBasics
import ThresholdHC.StoppingProgram.FlowBounds
import ThresholdHC.StoppingProgram.FlowConservation
import ThresholdHC.StoppingProgram.FlowCostMoment
import ThresholdHC.StoppingProgram.FlowMixture
import ThresholdHC.StoppingProgram.FlowOperations
import ThresholdHC.StoppingProgram.FlowPoisson
import ThresholdHC.StoppingProgram.FlowPotential
import ThresholdHC.StoppingProgram.FlowTableRates
import ThresholdHC.StoppingProgram.FourPriorMultipliers
import ThresholdHC.StoppingProgram.FractionalCutoff
import ThresholdHC.StoppingProgram.FullCapFlow
import ThresholdHC.StoppingProgram.FunctionMomentImage
import ThresholdHC.StoppingProgram.InformationBellman
import ThresholdHC.StoppingProgram.InformationBound
import ThresholdHC.StoppingProgram.InformationFiniteness
import ThresholdHC.StoppingProgram.InformationIncrement
import ThresholdHC.StoppingProgram.LabelPerspective
import ThresholdHC.StoppingProgram.MidpointComparison
import ThresholdHC.StoppingProgram.MidpointInformation
import ThresholdHC.StoppingProgram.MinimaxSelection
import ThresholdHC.StoppingProgram.MixtureStatistics
import ThresholdHC.StoppingProgram.Model
import ThresholdHC.StoppingProgram.MomentImage
import ThresholdHC.StoppingProgram.NullPruning
import ThresholdHC.StoppingProgram.ObservableInformation
import ThresholdHC.StoppingProgram.OrderedAffinity
import ThresholdHC.StoppingProgram.OrderedHellinger
import ThresholdHC.StoppingProgram.OrderedInformationBound
import ThresholdHC.StoppingProgram.OrderedPrefix
import ThresholdHC.StoppingProgram.OrderedRewards
import ThresholdHC.StoppingProgram.OrderedStoppedLaw
import ThresholdHC.StoppingProgram.OrderedWeights
import ThresholdHC.StoppingProgram.OrderedWork
import ThresholdHC.StoppingProgram.OutputChoices
import ThresholdHC.StoppingProgram.PascalFlow
import ThresholdHC.StoppingProgram.Perspective
import ThresholdHC.StoppingProgram.PerspectiveMonotonic
import ThresholdHC.StoppingProgram.PoissonMoments
import ThresholdHC.StoppingProgram.PolicyFlow
import ThresholdHC.StoppingProgram.PolicyMixture
import ThresholdHC.StoppingProgram.PolicyWeights
import ThresholdHC.StoppingProgram.PositiveTables
import ThresholdHC.StoppingProgram.PositiveValue
import ThresholdHC.StoppingProgram.PrefixCoefficients
import ThresholdHC.StoppingProgram.PrefixInformation
import ThresholdHC.StoppingProgram.PrefixModulus
import ThresholdHC.StoppingProgram.PrefixRisk
import ThresholdHC.StoppingProgram.PriceMultipliers
import ThresholdHC.StoppingProgram.PriceRatio
import ThresholdHC.StoppingProgram.PrimalAttainment
import ThresholdHC.StoppingProgram.PrimalCompactness
import ThresholdHC.StoppingProgram.PriorContraction
import ThresholdHC.StoppingProgram.PriorMixtures
import ThresholdHC.StoppingProgram.ProgramGeometry
import ThresholdHC.StoppingProgram.ProgramMultipliers
import ThresholdHC.StoppingProgram.ProgramUpper
import ThresholdHC.StoppingProgram.RareCompactness
import ThresholdHC.StoppingProgram.RarityMultiplier
import ThresholdHC.StoppingProgram.RarityOptimality
import ThresholdHC.StoppingProgram.RaritySupport
import ThresholdHC.StoppingProgram.RarityTheorem
import ThresholdHC.StoppingProgram.RawFlowConstruction
import ThresholdHC.StoppingProgram.RealizedOutputs
import ThresholdHC.StoppingProgram.RobustConstraints
import ThresholdHC.StoppingProgram.RobustRarity
import ThresholdHC.StoppingProgram.ShiftEstimator
import ThresholdHC.StoppingProgram.Slater
import ThresholdHC.StoppingProgram.Specification
import ThresholdHC.StoppingProgram.StrongDuality
import ThresholdHC.StoppingProgram.SublevelBounds
import ThresholdHC.StoppingProgram.TableCall
import ThresholdHC.StoppingProgram.TableExpansion
import ThresholdHC.StoppingProgram.TableStatistics
import ThresholdHC.StoppingProgram.TapeMoments
import ThresholdHC.StoppingProgram.TruncatedPrefix
import ThresholdHC.StoppingProgram.TruncationComparison
import ThresholdHC.StoppingProgram.TruncationLimit
import ThresholdHC.StoppingProgram.TruncationRisk
import ThresholdHC.StoppingProgram.WeakDuality
import ThresholdHC.StoppingProgram.WordFlow
import ThresholdHC.StoppingProgram.WordStopping

namespace Audit_entropy_tail_upper

open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile ThresholdHC.RareAboveTwo
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal 28000*selectionValue μ ρ B :=
  fun μ _ _ _ => ThresholdHC.EntropyTailExecution.entropy_tail_upper_28000 μ
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal 30001*closedQuantileValue μ ρ B :=
  fun μ _ _ _ => ThresholdHC.EntropyTailExecution.closed_quantile_upper_30001 μ

example : ThresholdHC.EntropyTailQuantile.QuantileSplitStatement := ThresholdHC.EntropyTailQuantile.quantile_split
example : ThresholdHC.EntropyTailQuantile.QuantileComparisonStatement := ThresholdHC.EntropyTailQuantile.quantile_comparison
example : ThresholdHC.EntropyTailQuantile.EntropyTailUpperStatement := ThresholdHC.EntropyTailExecution.entropy_tail_upper
example : ThresholdHC.EntropyTailQuantile.ClosedQuantileUpperStatement := ThresholdHC.EntropyTailExecution.closed_quantile_upper

end Audit_entropy_tail_upper

namespace Audit_stopping_components

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open ThresholdHC.StoppingProgram ThresholdHC.CapIdentification
example : ∀ (r w : ℕ → ℕ → ℝ) (κ : ℝ) (d : ℕ),
    (∀ a : StopTree d × StopTree d,
      rootInformation r d a-κ*rootWork w d a ≤ rootBellman r w κ d) ∧
    ∃ a : StopTree d × StopTree d,
      rootInformation r d a-κ*rootWork w d a = rootBellman r w κ d := rootBellman_maximum
example : ∀ (r w : ℕ → ℕ → ℝ), (∀ n k, 0 ≤ w n k) → ∀ d κ,
    rootBellman r w κ d = 0 ↔ κ = ratioValue (rootInformation r d) (rootWork w d) := rootBellman_zero_iff
example : ∀ {N : ℕ} (f : Flow N), FlowCone f → intensity f = 0 → ∀ s : CountState N,
    f.stopWeight s = 0 ∧ f.continueWeight s = 0 ∧ f.outputWeight s = 0 := flow_zero_intensity
example : ∀ {m : ℕ} (d : Fin m → ℝ) (N : ℕ), (∀ i, 0 < d i) → Function.Injective d → 0 < m →
    ((∀ g : Fin m → ℝ,
      (∀ j : Fin ((N+1)/2), (∑ i, g i*(d i)^(2*j.val+1)) = 0) → (∑ i, g i) = 0) ↔
        2*m-1 ≤ N) := moments_cap_threshold
example : ∀ (μ : Measure ThresholdHC.Tier6.Gap) [IsFiniteMeasure μ]
    (qH qL : ThresholdHC.Tier6.SignLaw) (N : ℕ),
    (∀ j : Fin ((N+1)/2), ∫ d, (qH.val d-qL.val d)*(d:ℝ)^(2*j.val+1) ∂μ = 0) ↔
      ∀ s : CountState N, countCoefficient μ qH s = countCoefficient μ qL s :=
  odd_moments_iff_count_match
example : ∀ (μ : Measure ThresholdHC.Tier6.Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    informationRatio μ N Q = 0 ↔
      ∀ j : Fin ((N+1)/2), ∫ d, (Q.high.val d-Q.low.val d)*(d:ℝ)^(2*j.val+1) ∂μ = 0 :=
  informationRatio_zero_iff_moments
example : ∀ (μ : Measure ThresholdHC.Tier6.Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (N : ℕ) (S : Finset ThresholdHC.Tier6.Gap),
    μ.support = (S:Set ThresholdHC.Tier6.Gap) → 0 < S.card →
    ((∀ qH qL : ThresholdHC.Tier6.SignLaw,
      ThresholdHC.RareAboveTwo.RarePrior μ ρ qH → ThresholdHC.RareAboveTwo.RarePrior μ ρ qL →
      (∀ s : CountState N, countCoefficient μ qH s = countCoefficient μ qL s) →
      ThresholdHC.Tier6.signMean μ qH.val = ThresholdHC.Tier6.signMean μ qL.val) ↔
      2*S.card-1 ≤ N) := finite_support_target_threshold
example : ∀ (μ : Measure ThresholdHC.Tier6.Gap) [IsProbabilityMeasure μ],
    μ.support.Infinite → ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ N : ℕ,
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ B : ℝ, c ≤ programSquared μ ρ B N := infinite_support_program_floor
example : ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure ThresholdHC.Tier6.Gap) [IsProbabilityMeasure μ]
    (ν : Measure R) [IsProbabilityMeasure ν] (qH qL : ThresholdHC.Tier6.SignLaw) (N : ℕ),
    (∀ j : Fin ((N+1)/2), ∫ d, (qH.val d-qL.val d)*(d:ℝ)^(2*j.val+1) ∂μ = 0) →
    ∀ (A : ThresholdHC.CriticalEntropy.StoppedProcedure R E), (∀ z, A.stop z ≤ N) →
    ThresholdHC.CriticalEntropy.cappedTranscriptLaw μ ν
      (ThresholdHC.ObservableSimulation.gapParameter false) (ThresholdHC.ObservableSimulation.gapParameter true)
      (ThresholdHC.ObservableSimulation.signUnit qH) A N =
    ThresholdHC.CriticalEntropy.cappedTranscriptLaw μ ν
      (ThresholdHC.ObservableSimulation.gapParameter false) (ThresholdHC.ObservableSimulation.gapParameter true)
      (ThresholdHC.ObservableSimulation.signUnit qL) A N := stopped_law_eq_of_odd_moments
example : ∀ (μ : Measure ThresholdHC.Tier6.Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ N : ℕ, 0 < N →
    (∃ qH qL : ThresholdHC.Tier6.SignLaw,
      ThresholdHC.RareAboveTwo.RarePrior μ ρ qH ∧ ThresholdHC.RareAboveTwo.RarePrior μ ρ qL ∧
      (∀ j : Fin ((N+1)/2), ∫ d, (qH.val d-qL.val d)*(d:ℝ)^(2*j.val+1) ∂μ = 0) ∧
      capDiameter μ ρ N = ThresholdHC.Tier6.signMean μ qH.val-ThresholdHC.Tier6.signMean μ qL.val ∧
      ∀ rH rL : ThresholdHC.Tier6.SignLaw,
        ThresholdHC.RareAboveTwo.RarePrior μ ρ rH → ThresholdHC.RareAboveTwo.RarePrior μ ρ rL →
        (∀ j : Fin ((N+1)/2), ∫ d, (rH.val d-rL.val d)*(d:ℝ)^(2*j.val+1) ∂μ = 0) →
        ThresholdHC.Tier6.signMean μ rH.val-ThresholdHC.Tier6.signMean μ rL.val ≤ capDiameter μ ρ N) ∧
    Tendsto (fun B : ℝ => programValue μ ρ B N) atTop (𝓝 (ENNReal.ofReal (capDiameter μ ρ N/2))) ∧
    (∀ S : Finset ThresholdHC.Tier6.Gap, μ.support = (S:Set ThresholdHC.Tier6.Gap) → 0 < S.card →
      (capDiameter μ ρ N = 0 ↔ 2*S.card-1 ≤ N)) ∧
    (μ.support.Infinite → 0 < capDiameter μ ρ N) := fixed_cap_identification
example : ∀ (μ : Measure ThresholdHC.Tier6.Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ), 0 < B → ∀ N : ℕ,
    dualValue μ ρ B N ≤ programSquared μ ρ B N := fun μ _ ρ B hB N => weak_duality μ hB N
example : ∀ (N : ℕ) (μ : Measure ThresholdHC.Tier6.Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ), 0 < ρ → ρ ≤ 1/2 → 0 < B →
    programSquared μ ρ B N = dualValue μ ρ B N ∧
      ∃ Q : FourPriors, Admissible μ ρ Q ∧ dualRatio μ B N Q = programSquared μ ρ B N ∧
        0 < programSquared μ ρ B N ∧ informationRatio μ N Q < ⊤ :=
  fun N μ _ ρ B hρ hρhalf hB => strong_four_prior_duality N μ hρ hρhalf hB


end Audit_stopping_components

namespace Audit_stopping_dual

open MeasureTheory
open scoped ENNReal
open ThresholdHC.StoppingProgram
example : AttainedDualStatement := attained_four_prior_dual
example : ∀ (μ : Measure ThresholdHC.Tier6.Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (N : ℕ), 0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < N →
    programSquared μ ρ B N = dualValue μ ρ B N ∧
    ∃ (C : Certificate N) (Q : FourPriors),
      Feasible μ ρ B C ∧ Admissible μ ρ Q ∧
      certificateSquared C = programSquared μ ρ B N ∧
      dualRatio μ B N Q = programSquared μ ρ B N ∧
      0 < programSquared μ ρ B N ∧ informationRatio μ N Q < ⊤ := attained_four_prior_dual


end Audit_stopping_dual

namespace Audit_rarity_support

open MeasureTheory
open scoped ENNReal
open ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)
example : ∀ (μ : Measure Gap) (ρ : ℝ) (f : Gap → ℝ),
    rareFunctional μ ρ f = sSup {r : ℝ | ∃ q : SignLaw,
      ThresholdHC.RareAboveTwo.RarePrior μ ρ q ∧ r = ∫ d, q.val d*f d ∂μ} := rareFunctional_eq_sSup
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ M : ℝ), 0 < ρ → 0 ≤ M →
    ∀ f : Gap → ℝ, Measurable f → MemLp f 2 μ → (∀ᵐ d ∂μ, f d ≤ M) →
    ∃ (ell c : ℝ) (q : SignLaw), 0 ≤ ell ∧ ell ≤ M ∧ 0 ≤ c ∧ c ≤ 1 ∧
      (∀ d, q.val d = if ell < f d then 1 else if f d = ell then c else 0) ∧
      signMean μ q.val ≤ ρ ∧
      sSup {r : ℝ | ∃ p : SignLaw, signMean μ p.val ≤ ρ ∧ r = ∫ d, p.val d*f d ∂μ} =
        ∫ d, q.val d*f d ∂μ ∧
      (∫ d, q.val d*f d ∂μ) = ρ*ell+∫ d, max (f d-ell) 0 ∂μ ∧
      (∀ t : ℝ, 0 ≤ t → ρ*ell+(∫ d, max (f d-ell) 0 ∂μ) ≤
        ρ*t+∫ d, max (f d-t) 0 ∂μ) ∧
      (0 < ell → signMean μ q.val = ρ) :=
  fun μ _ ρ M hρ hM f hf hLp hb => fractional_rarity_support_explicit μ hρ hM f hf hLp hb


end Audit_rarity_support

namespace Audit_finite_stopping_program

open MeasureTheory Polynomial
open scoped ENNReal BigOperators
open ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw)
example : ∀ {I : Type} [Fintype I] (μ : Measure Gap) (w : I → ℝ) (d : I → Gap),
    (∀ i, 0 ≤ w i) → (μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i)) →
    ∀ (ρ : ℝ) (P : ℝ[X]) (z : ℝ),
    (∃ (ell : ℝ) (u : I → ℝ), 0 ≤ ell ∧ (∀ i, 0 ≤ u i ∧ P.eval (d i:ℝ)-ell ≤ u i) ∧
      ρ*ell+∑ i, w i*u i ≤ z) ↔
    ∃ ell, 0 ≤ ell ∧ ρ*ell+(∫ x : Gap, max (P.eval (x:ℝ)-ell) 0 ∂μ) ≤ z :=
  by
    intro I inst μ w d hw hμ ρ P z
    exact finiteTailBound_iff μ w d hw hμ ρ P z
example : ∀ {I : Type} [Fintype I] {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (w : I → ℝ) (d : I → Gap), (∀ i, 0 ≤ w i) →
    (μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i)) →
    ∀ ρ B, 0 < ρ → ∀ C : Certificate N,
    Feasible μ ρ B C ↔ FlowCone C.flow ∧ 0 ≤ C.bias ∧ 0 ≤ C.variance ∧
      FiniteTailBound w d ρ (biasPolynomial C)
        (C.bias-(C.offset+finiteNullMean w d C.flow.outputWeight)) ∧
      FiniteTailBound w d ρ (-biasPolynomial C)
        (C.bias+(C.offset+finiteNullMean w d C.flow.outputWeight)) ∧
      FiniteTailBound w d ρ (countMeanPolynomial C.flow.momentWeight)
        (C.variance-finiteNullMean w d C.flow.momentWeight) ∧
      FiniteTailBound w d ρ (countMeanPolynomial C.flow.continueWeight)
        (B-finiteNullMean w d C.flow.continueWeight) :=
  by
    intro I inst N μ prob w d hw hμ ρ B hρ C
    exact feasible_iff_finite_program μ w d hw hμ hρ C


end Audit_finite_stopping_program

namespace Audit_stopping_flow_mixture

open MeasureTheory
open scoped BigOperators
open ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw)
example : ∀ {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (f : Flow N),
    FlowCone f → countMean μ q f.stopWeight = intensity f := countMean_stop_eq_intensity
example : ∀ {N : ℕ} (f : Flow N), FlowCone f → ∀ (r w : ℕ → ℕ → ℝ) (κ : ℝ), w 0 0 = 1 →
    (∑ n ∈ Finset.range (N+1), ∑ k ∈ Finset.range (n+1),
      (rawArray f.stopWeight n k*r n k-κ*rawArray f.continueWeight n k*w n k)) ≤
        intensity f*rootBellman r w κ (N-1) := flowScore_le_rootBellman
example : ∀ {N : ℕ} (f : Flow N), FlowCone f → ∀ s : CountState N,
    (∑ b : CountState N → Bool, decisionWeight (flowDecisionParameters f) b*
      (policyArrival (intensity f) (countDecision b) s.1.val s.2.val*countDecision b s.1.val s.2.val)) =
        rawArray f.stopWeight s.1.val s.2.val ∧
    (∑ b : CountState N → Bool, decisionWeight (flowDecisionParameters f) b*
      (policyArrival (intensity f) (countDecision b) s.1.val s.2.val*(1-countDecision b s.1.val s.2.val))) =
        rawArray f.continueWeight s.1.val s.2.val := flow_mixture_weights
example : ∀ {N : ℕ} (f : Flow N), FlowCone f → 0 < N →
    (∀ b, 0 ≤ decisionWeight (flowDecisionParameters f) b) ∧
    (∑ b : CountState N → Bool, decisionWeight (flowDecisionParameters f) b) = 1 ∧
    ∀ b : CountState N → Bool, 0 < decisionWeight (flowDecisionParameters f) b →
      b (rootState N) = false ∧ ∀ s : CountState N, s.1.val = N → b s = true := by
  intro N f hf hN
  exact ⟨(flow_mixture_probability f hf).1,(flow_mixture_probability f hf).2,
    fun b hb => flow_mixture_supported_tables f hf hN b hb⟩
example : ∀ {N : ℕ} (hN : 0 < N) (b : CountState N → Bool) (y : CountState N → ℝ),
    ∀ ω : ℕ → Bool, (tableCall hN b y).cost ω ≤ N ∧
      (tableCall hN b y).value ω = y (tableStoppedState b ω) ∧
      ‖(tableCall hN b y).value ω‖ ≤ ∑ s, ‖y s‖ := by
  intro N hN b y ω
  exact ⟨tableCall_cost_le hN b y ω,tableValue_eq b y ω,tableValue_bounded b y ω⟩


end Audit_stopping_flow_mixture

namespace Audit_stopping_program_upper

open MeasureTheory
open scoped ENNReal
open ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
example : ProgramUpperStatement := program_upper
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (N : ℕ),
    0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < N →
    rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N := program_upper
example : ∀ {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (C : Certificate N),
    Feasible μ ρ B C → 0 < N →
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      RareBudget μ A ρ B ∧ ∀ q : SignLaw, RarePrior μ ρ q →
        squaredRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val) ≤
          ENNReal.ofReal (C.bias^2+C.variance) := certificate_realization


end Audit_stopping_program_upper

namespace Audit_reference_absorption

open MeasureTheory
open scoped ENNReal
open ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (N : ℕ),
    0 < ρ → ρ ≤ 1/2 → 0 < B →
    midpointValue μ ρ B N ≤ programValue μ ρ B N ∧
      programValue μ ρ B N ≤ 3*midpointValue μ ρ B N := midpoint_comparison
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (N : ℕ),
    0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < N →
    (⨆ (q : SignLaw) (r : SignLaw) (_ : RarePrior μ ρ q) (_ : RarePrior μ ρ r),
      dualRatio μ B N (midpointFourPriors q r)) ^ (1/(2:ℝ)) ≤ programValue μ ρ B N ∧
    programValue μ ρ B N ≤ 3*(⨆ (q : SignLaw) (r : SignLaw)
      (_ : RarePrior μ ρ q) (_ : RarePrior μ ρ r),
      dualRatio μ B N (midpointFourPriors q r)) ^ (1/(2:ℝ)) := by
  intro μ inst ρ B N hρ hρquarter hB _hN
  exact midpoint_comparison μ ρ B N hρ (by linarith) hB
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    informationRatio μ N (absorbedPriors Q) ≤ informationRatio μ N Q :=
  absorbedPriors_informationRatio_le


end Audit_reference_absorption

namespace Audit_information_bellman

open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap)
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    0 < N → informationRatio μ N Q ≠ ⊤ →
    informationRatio μ N Q = ENNReal.ofReal (bellmanRatio μ N Q) ∧
    (∀ κ : ℝ, rootBellman (prefixReward μ Q) (prefixCoefficient μ Q.work) κ (N-1) = 0 ↔
      κ = (informationRatio μ N Q).toReal) ∧
    ∃ p : ℕ → ℕ → ℝ, (∀ n k, p n k = 0 ∨ p n k = 1) ∧ p 0 0 = 0 ∧
      (∀ k, k ≤ N → p N k = 1) ∧ FlowCone (policyFlow N p) ∧ intensity (policyFlow N p) = 1 ∧
      flowInformation μ Q (policyFlow N p)/
        ENNReal.ofReal (countMean μ Q.work (policyFlow N p).continueWeight) = informationRatio μ N Q :=
  informationRatio_bellman
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors), 0 < N →
    (informationRatio μ N Q = ⊤ ↔ ∃ n k, n ≤ N ∧ k ≤ n ∧
      prefixCoefficient μ Q.variance n k = 0 ∧
      prefixCoefficient μ Q.high n k ≠ prefixCoefficient μ Q.low n k) := informationRatio_top_iff
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    0 < N → informationRatio μ N Q ≠ ⊤ → ∀ f : Flow N, FlowCone f →
    (∀ n k, n < N → k ≤ n → 0 ≤ informationIncrement μ Q n k) ∧
    (flowInformation μ Q f).toReal = ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (n+1),
      rawArray f.continueWeight n k*informationIncrement μ Q n k := informationRatio_increment_identity
example : ∀ (μ : Measure Gap) (N : ℕ) (Q : FourPriors),
    Continuous (fun κ => rootBellman (prefixReward μ Q) (prefixCoefficient μ Q.work) κ (N-1)) ∧
    StrictAnti (fun κ => rootBellman (prefixReward μ Q) (prefixCoefficient μ Q.work) κ (N-1)) := by
  intro μ N Q
  exact ⟨continuous_rootBellman _ _ _,rootBellman_strictAnti _ _ (prefixCoefficient_nonneg μ Q.work) _⟩
example : ∀ (r w : ℕ → ℕ → ℝ) (κ : ℝ) {N : ℕ}, 0 < N → w 0 0 = 1 →
    (∀ f : Flow N, FlowCone f → intensity f = 1 → rawFlowScore f r w κ ≤ rootBellman r w κ (N-1)) ∧
    ∃ f : Flow N, FlowCone f ∧ intensity f = 1 ∧ rawFlowScore f r w κ = rootBellman r w κ (N-1) :=
  flowScore_maximum


end Audit_information_bellman

namespace Audit_ordered_information

open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation
open ThresholdHC.Tier6 (Gap SignLaw)
example : ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E],
    ∀ (ν : Measure R) [IsFiniteMeasure ν] (A : StoppedProcedure R E) (N : ℕ),
    (∀ z, A.stop z ≤ N) → FlowCone (orderedFlow ν A N) := orderedFlow_cone
example : ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E],
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν],
    ∀ (q : SignLaw) (A : StoppedProcedure R E) (N : ℕ), (∀ z, A.stop z ≤ N) →
    populationExpectedWork μ ν (gapParameter false) (gapParameter true) (signUnit q) A =
      ENNReal.ofReal (countMean μ q (orderedFlow ν A N).continueWeight) := orderedFlow_actual_work
example : ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E],
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν],
    ∀ (q r : SignLaw) (A : StoppedProcedure R E) (N : ℕ), (∀ z, A.stop z ≤ N) →
    4*stoppedHellinger μ ν q r A N ≤ (flowInformation μ (midpointFourPriors q r) (orderedFlow ν A N)).toReal ∧
    (flowInformation μ (midpointFourPriors q r) (orderedFlow ν A N)).toReal ≤ 8*stoppedHellinger μ ν q r A N :=
  orderedFlow_midpoint_hellinger
example : ∀ {R E : Type} [MeasurableSpace R] [MeasurableSpace E],
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν],
    ∀ (q r : SignLaw) (A : StoppedProcedure R E) (N : ℕ), (∀ z, A.stop z ≤ N) →
    1-(hellingerAffinity
      (cappedTranscriptLaw μ ν (gapParameter false) (gapParameter true) (signUnit q) A N)
      (cappedTranscriptLaw μ ν (gapParameter false) (gapParameter true) (signUnit r) A N)).toReal ≤
      ((informationRatio μ N (midpointFourPriors q r)).toReal/4)*
      (populationExpectedWork μ ν (gapParameter false) (gapParameter true)
        (signUnit (ThresholdHC.StoppingProgram.midpointPrior q r)) A).toReal := ordered_stopped_hellinger_work


end Audit_ordered_information

namespace Audit_adaptive_information

open MeasureTheory
open scoped ENNReal
open ThresholdHC.StoppingProgram ThresholdHC.CriticalEntropy
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
example : ∀ {Ω : Type} [MeasurableSpace Ω],
    ∀ (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
    ∀ (f : Ω → ℝ), Measurable f → ∀ a b : ℝ,
    ENNReal.ofReal ((b-a)^2*(hellingerAffinity P Q).toReal^2/4) ≤
      max (squaredRisk P f a) (squaredRisk Q f b) := affinity_squared_risk
example : ∀ {Ω : Type} [MeasurableSpace Ω],
    ∀ (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
    ∀ (f : Ω → ℝ), Measurable f → ∀ a b : ℝ, a ≤ b →
    ENNReal.ofReal ((b-a)*(hellingerAffinity P Q).toReal/2) ≤
      max (rootMeanRisk P f a) (rootMeanRisk Q f b) := affinity_rms_risk
example : ∀ {R : Type} [MeasurableSpace R],
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R),
    ∀ (q r : SignLaw) (N : ℕ) (B : ℝ), 0 ≤ B →
    expectedWork μ A (ThresholdHC.StoppingProgram.midpointPrior q r) ≤ ENNReal.ofReal B →
    1-(hellingerAffinity
      ((experimentLaw μ A q).map (fun z => (z.1.1,processPrefix N z.2)))
      ((experimentLaw μ A r).map (fun z => (z.1.1,processPrefix N z.2)))).toReal ≤
      (informationRatio μ N (midpointFourPriors q r)).toReal/4*B := by
  intro R _ μ _ A q r N B hB hw
  simpa only [observablePrefixLaw] using observable_prefix_information_budget μ A q r N B hB hw
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    ∀ (q r : SignLaw) (s : ℝ) (hs : 0 ≤ s ∧ s ≤ 1),
    signMean μ (contractPrior r q s hs).val-signMean μ (contractPrior q r s hs).val =
      s*(signMean μ r.val-signMean μ q.val) := contractPrior_gap
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
    ∀ (N : ℕ) (q r : SignLaw) (s : ℝ) (hs : 0 ≤ s ∧ s ≤ 1),
    informationRatio μ N (midpointFourPriors (contractPrior q r s hs) (contractPrior r q s hs)) =
      ENNReal.ofReal (s^2)*informationRatio μ N (midpointFourPriors q r) := contractPrior_informationRatio
example : ∀ {R : Type} [MeasurableSpace R],
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R),
    ∀ (q r : SignLaw) (N : ℕ) (B : ℝ), 0 ≤ B →
    expectedWork μ A (ThresholdHC.StoppingProgram.midpointPrior q r) ≤ ENNReal.ofReal B →
    signMean μ q.val ≤ signMean μ r.val →
    ∀ (f : R × (Fin N → Option Bool) → ℝ), Measurable f →
    ENNReal.ofReal ((signMean μ r.val-signMean μ q.val)/2 *
      (1-(informationRatio μ N (midpointFourPriors q r)).toReal*B/4)) ≤
        max (rootMeanRisk (observablePrefixLaw μ A q N) f (signMean μ q.val))
          (rootMeanRisk (observablePrefixLaw μ A r N) f (signMean μ r.val)) := observable_prefix_risk
example : ∀ {R : Type} [MeasurableSpace R],
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R),
    ∀ (ρ B : ℝ), 0 < ρ → ρ ≤ 1/2 → 0 < B → RareBudget μ A ρ B →
    ∀ (N : ℕ) (f : R × (Fin N → Option Bool) → ℝ), Measurable f →
    ∀ T : ℝ≥0∞, (∀ u : SignLaw, RarePrior μ ρ u →
      rootMeanRisk (observablePrefixLaw μ A u N) f (signMean μ u.val) ≤ T) →
    programValue μ ρ B N ≤ 8*T := prefix_program_bound


end Audit_adaptive_information

namespace Audit_finite_risk_certificate

open MeasureTheory
open scoped ENNReal
open ThresholdHC.StoppingProgram ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
example : FiniteCertificateStatement := finite_certificate
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
    rareMinimaxRisk μ ρ B ≤ programValue μ ρ B (⌈64*max B (ρ*B^2)⌉₊) ∧
    programValue μ ρ B (⌈64*max B (ρ*B^2)⌉₊) ≤ 16*rareMinimaxRisk μ ρ B := finite_certificate
example : ProgramUpperStatement := program_upper
example : AttainedDualStatement := attained_four_prior_dual
example : ∀ {R : Type} [MeasurableSpace R],
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R),
    ∀ ρ B : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B → RareBudget μ A ρ B →
    ENNReal.ofReal ((1/16:ℝ)*min ρ (Real.sqrt (ρ/B))) ≤ rareRisk μ A ρ := bernoulli_label_floor
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
    ENNReal.ofReal ((1/16:ℝ)*min ρ (Real.sqrt (ρ/B))) ≤ rareMinimaxRisk μ ρ B := bernoulli_label_minimax_floor
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/2 → 0 < B → ∀ N : ℕ,
    programValue μ ρ B N ≤ 8*(rareMinimaxRisk μ ρ B+
      ENNReal.ofReal (ρ/2*Real.sqrt (B/((N:ℝ)+1)))) := program_le_minimax_truncation
example : ∀ {R : Type} [MeasurableSpace R],
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw),
    ∀ ρ θ B : ℝ, 0 ≤ ρ → (0 ≤ θ ∧ θ ≤ ρ) → 0 ≤ B →
    ∀ N : ℕ, expectedWork μ A q ≤ ENNReal.ofReal B →
    rootMeanRisk (observablePrefixLaw μ A q N) (prefixTruncation A ρ N) θ ≤
      rootMeanRisk (experimentLaw μ A q) (populationOutput A) θ+
        ENNReal.ofReal (ρ/2*Real.sqrt (B/((N:ℝ)+1))) := prefixTruncation_rmsRisk


end Audit_finite_risk_certificate

namespace Audit_infinite_cap_dual

open MeasureTheory Filter
open scoped ENNReal Topology
open ThresholdHC.Genie ThresholdHC.StoppingProgram ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], ∀ {ρ B : ℝ},
    0 < ρ → ρ ≤ 1/2 → 0 < B →
    infiniteProgramValue μ ρ B ^ 2 = infiniteDualValue μ ρ B ∧
    ∃ Q : FourPriors, Admissible μ ρ Q ∧
      infiniteDualRatio μ B Q = infiniteProgramValue μ ρ B ^ 2 := infinite_four_prior_duality
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], ∀ {ρ B : ℝ},
    0 < ρ → ρ ≤ 1/4 → 0 < B →
    ∃ Q : FourPriors, Admissible μ ρ Q ∧
      infiniteDualRatio μ B Q = infiniteProgramValue μ ρ B ^ 2 ∧
      0 < infiniteProgramValue μ ρ B ^ 2 ∧ infiniteInformationRatio μ Q < ⊤ := infinite_dual_positive_attained
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/2 → 0 < B →
    infiniteMidpointValue μ ρ B ≤ infiniteProgramValue μ ρ B ∧
    infiniteProgramValue μ ρ B ≤ 3*infiniteMidpointValue μ ρ B := infinite_midpoint_comparison
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/2 → 0 < B →
    rareMinimaxRisk μ ρ B ≤ infiniteProgramValue μ ρ B ∧
    infiniteProgramValue μ ρ B ≤ 8*rareMinimaxRisk μ ρ B := infinite_program_comparison
example : ∀ (μ : Measure Gap) (Q : FourPriors),
    Monotone (fun N => informationRatio μ N Q) := informationRatio_mono
example : ∀ (μ : Measure Gap) (ρ B : ℝ),
    Antitone (fun N => programValue μ ρ B N) := programValue_antitone
example : ∀ (μ : Measure Gap) (ρ B : ℝ),
    Tendsto (fun N : ℕ => programValue μ ρ B (N+1)) atTop
      (𝓝 (infiniteProgramValue μ ρ B)) := programValue_tendsto
example : ∀ (μ : Measure Gap) (Q : FourPriors),
    Tendsto (fun N : ℕ => informationRatio μ (N+1) Q) atTop
      (𝓝 (infiniteInformationRatio μ Q)) := informationRatio_tendsto


end Audit_infinite_cap_dual

namespace Audit_genie_brackets

open MeasureTheory
open scoped ENNReal
open ThresholdHC.Genie ThresholdHC.StoppingProgram ThresholdHC.Tier6
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (N : ℕ), 0 < N → ∀ Q : FourPriors,
    infiniteInformationRatio μ Q ≤ genieInformationRatio μ N Q := infiniteInformationRatio_le_genie
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (Q : FourPriors),
    Antitone (fun N : ℕ => genieInformationRatio μ (N+1) Q) := genieInformationRatio_antitone
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    latentDivergence μ Q ≠ ⊤ → genieInformationRatio μ N Q-informationRatio μ N Q ≤
      latentDivergence μ Q-terminalInformation μ Q N := genie_information_error
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    0 < N → latentDivergence μ Q ≠ ⊤ →
    genieInformationRatio μ N Q = ENNReal.ofReal (genieBellmanRatio μ N Q) ∧
    let f := bellmanFlow (genieReward μ Q N) (prefixCoefficient μ Q.work) (genieBellmanRatio μ N Q) N
    FlowCone f ∧ intensity f = 1 ∧ genieFlowInformation μ Q f /
      ENNReal.ofReal (countMean μ Q.work f.continueWeight) = genieInformationRatio μ N Q :=
  genieInformationRatio_bellman_attained
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ) (Q : FourPriors),
    0 < N → latentDivergence μ Q ≠ ⊤ → ∀ κ : ℝ, 0 ≤ κ →
    (genieInformationRatio μ N Q ≤ ENNReal.ofReal κ ↔
      rootBellman (genieReward μ Q N) (prefixCoefficient μ Q.work) κ (N-1) ≤ 0) :=
  genieInformationRatio_bellman_certificate
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (N : ℕ), 0 < N → ∀ Q : FourPriors,
    (genieInformationRatio μ N Q = ⊤ ↔ latentDivergence μ Q = ⊤) := genieInformationRatio_top_iff
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (Q : FourPriors) (n k : ℕ),
    prefixInformation μ Q n k ≤ revealReward μ Q n k := prefixInformation_le_revealReward
example : ∀ (μ : Measure Gap) (Q : FourPriors) (N : ℕ),
    genieFlowInformation μ Q (fullCapFlow N) = latentDivergence μ Q := genieFlowInformation_fullCap


end Audit_genie_brackets

namespace Audit_genie_convergence

open MeasureTheory Filter
open scoped ENNReal Topology
open ThresholdHC.Genie ThresholdHC.StoppingProgram ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (Q : FourPriors), latentDivergence μ Q ≠ ⊤ →
    (∫⁻ z, ENNReal.ofReal ((latentScore Q z)^2) ∂latentReference μ Q.variance) = latentDivergence μ Q :=
  latentScore_secondMoment
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors), latentDivergence μ Q ≠ ⊤ →
    ∀ n : ℕ, (∫⁻ z, ENNReal.ofReal ((((latentTapeLaw μ Q.variance)[latentTapeScore Q |
      observationFiltration latentObservedTape measurable_latentObservedTape n]) z)^2)
        ∂latentTapeLaw μ Q.variance) = terminalInformation μ Q n := posterior_secondMoment_eq_terminal
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors), latentDivergence μ Q ≠ ⊤ →
    let P := latentTapeLaw μ Q.variance
    let ℱ := observationFiltration latentObservedTape measurable_latentObservedTape
    ∀ᵐ z ∂P, Tendsto (fun n => (P[latentTapeScore Q | ℱ n]) z) atTop (𝓝 (latentTapeScore Q z)) :=
  latent_score_posterior_tendsto
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors), latentDivergence μ Q ≠ ⊤ →
    Tendsto (terminalInformation μ Q) atTop (𝓝 (latentDivergence μ Q)) := terminalInformation_tendsto
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors), latentDivergence μ Q ≠ ⊤ →
    Tendsto (revealResidual μ Q) atTop (𝓝 0) := revealResidual_tendsto_zero
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors), latentDivergence μ Q ≠ ⊤ →
    Tendsto (fun n : ℕ => genieInformationRatio μ (n+1) Q) atTop (𝓝 (infiniteInformationRatio μ Q)) :=
  genieInformationRatio_tendsto
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors) (ε : ℝ)
    (hε : 0 ≤ ε ∧ ε ≤ 1), 0 < ε →
    latentDivergence μ (regularizedPriors Q ε hε) ≤ ENNReal.ofReal (4/ε) := regularized_latentDivergence_bound
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors) (ε : ℝ)
    (hε : 0 ≤ ε ∧ ε ≤ 1), ε < 1 → infiniteInformationRatio μ (regularizedPriors Q ε hε) ≤
      ENNReal.ofReal (1/(1-ε))*infiniteInformationRatio μ Q := regularized_infiniteInformation
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}, 0 < ρ → ρ ≤ 1/2 → 0 < B →
    (⨆ n : ℕ, genieSquared μ ρ B (n+1)) = infiniteProgramValue μ ρ B ^ 2 := genieSquared_sup_eq_infinite
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}, 0 < ρ → ρ ≤ 1/2 → 0 < B →
    Tendsto (fun n : ℕ => genieValue μ ρ B (n+1)) atTop (𝓝 (infiniteProgramValue μ ρ B)) := genieValue_tendsto
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ), 0 < ρ → ρ ≤ 1/2 → 0 < B →
    ∀ N : ℕ, 0 < N → genieValue μ ρ B N/8 ≤ rareMinimaxRisk μ ρ B ∧
      rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N := genie_risk_bracket
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}, 0 < ρ → ρ ≤ 1/2 → 0 < B →
    ∃ N : ℕ, 0 < N ∧ programValue μ ρ B N ≤ 2*genieValue μ ρ B N ∧
      rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N ∧ programValue μ ρ B N ≤ 16*rareMinimaxRisk μ ρ B :=
  genie_stopping_terminates


end Audit_genie_convergence

namespace Audit_genie_conic

open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.Genie ThresholdHC.StoppingProgram ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
example : ∀ t x : ℝ, 0 ≤ t → 0 ≤ x →
    IsGreatest ((directRiskProfile t x) '' Set.Icc (0:ℝ) 1)
      (directRiskProfile t x (directRiskScale x)) := directRiskProfile_greatest
example : ∀ t x : ℝ, 0 ≤ x →
    (directRiskProfile t x (directRiskScale x))^2 =
      if x ≤ 4/3 then t^2/4*(1-x/4)^2 else 4*t^2/(27*x) := directRiskProfile_square
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ), 0 ≤ ρ → 0 ≤ B →
    ∀ Q : FourPriors, Admissible μ ρ Q → signMean μ Q.low.val ≤ signMean μ Q.high.val →
    ∀ N : ℕ, 0 < N → ∀ κ : ℝ, 0 ≤ κ → genieInformationRatio μ N Q ≤ ENNReal.ofReal κ →
    ENNReal.ofReal (directRiskSquared ((signMean μ Q.high.val-signMean μ Q.low.val)/3) (B*κ)) ≤
      rareMinimaxRisk μ ρ B ^ 2 := genie_direct_squared_risk
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ), 0 ≤ ρ → 0 ≤ B →
    ∀ Q : FourPriors, Admissible μ ρ Q → signMean μ Q.low.val ≤ signMean μ Q.high.val →
    latentDivergence μ Q ≠ ⊤ → ∀ N : ℕ, 0 < N → ∀ κ : ℝ, 0 ≤ κ →
    rootBellman (genieReward μ Q N) (prefixCoefficient μ Q.work) κ (N-1) ≤ 0 →
    ENNReal.ofReal (directRiskSquared ((signMean μ Q.high.val-signMean μ Q.low.val)/3) (B*κ)) ≤
      rareMinimaxRisk μ ρ B ^ 2 := genie_bellman_direct_squared_risk
variable {I : Type*} [Fintype I]
example : ∀ (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (w : I → ℝ) (d : I → Gap),
    (∀ i, 0 < w i) → μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i) →
    ∀ Q : FourPriors, 0 < N → ∀ α η : ℝ, 0 < α → 0 ≤ η →
    ((∃ X rp rm, FiniteGenieCones (N := N) μ w d Q α η X rp rm) ↔
      genieInformationRatio μ N Q ≤ ENNReal.ofReal (4*η/α^2)) := finiteGenieCones_iff_price
example : ∀ (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (w : I → ℝ) (d : I → Gap),
    (∀ i, 0 < w i) → μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i) →
    ∀ B : ℝ, 0 < B → ∀ Q : FourPriors, 0 < N →
    ∃ (α η : ℝ) (X : CountState N → ℝ) (rp rm : I → ℝ), 0 ≤ α ∧ 0 ≤ η ∧
      FiniteGenieCones μ w d Q α η X rp rm ∧
      ENNReal.ofReal (α*(signMean μ Q.high.val-signMean μ Q.low.val)-α^2-η*B) = genieDualRatio μ B N Q :=
    finiteGenieCones_objective_attained
example : ∀ {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ] (w : I → ℝ) (d : I → Gap),
    (∀ i, 0 ≤ w i) → μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i) → Function.Injective d →
    ∀ ρ B : ℝ, 0 ≤ ρ → ∀ v : AtomConicPoint I N, AtomConicFeasible w d ρ v →
    ∃ Q : FourPriors, Admissible μ ρ Q ∧
      FiniteGenieCones μ w d Q v.scale v.price v.bellman v.revealPlus v.revealMinus ∧
      atomConicObjective w B v ≤ v.scale*(signMean μ Q.high.val-signMean μ Q.low.val)-v.scale^2-v.price*B :=
    atomConic_realization
example : ∀ (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (w : I → ℝ) (d : I → Gap),
    (∀ i, 0 < w i) → μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i) → Function.Injective d →
    ∀ ρ B : ℝ, 0 ≤ ρ → 0 < B → 0 < N →
    atomConicValue N w d ρ B = genieSquared μ ρ B N := atomConicValue_eq_genieSquared
example : ∀ (I : Type*) [Fintype I] (N : ℕ),
    atomConicVariableCount I N ≤ 3+6*Fintype.card I+(N+1)^2 := atomConicVariableCount_bound


end Audit_genie_conic

namespace Audit_genie_counterexample

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators
open ThresholdHC.Genie ThresholdHC.StoppingProgram ThresholdHC.Tier6
example : Admissible uniformGapLaw (1/4) singularExamplePriors ∧
    latentDivergence uniformGapLaw singularExamplePriors = ⊤ ∧
    (∀ N : ℕ, 0 < N → genieInformationRatio uniformGapLaw N singularExamplePriors = ⊤) ∧
    infiniteInformationRatio uniformGapLaw singularExamplePriors ≤ ENNReal.ofReal (3/4) ∧
    ¬Tendsto (fun n : ℕ => genieInformationRatio uniformGapLaw (n+1) singularExamplePriors)
      atTop (𝓝 (infiniteInformationRatio uniformGapLaw singularExamplePriors)) := infinite_divergence_counterexample
example : ∀ {N : ℕ} (f : Flow N), FlowCone f →
    flowInformation uniformGapLaw singularExamplePriors f ≤
      ENNReal.ofReal (3/4*countMean uniformGapLaw singularExamplePriors.work f.continueWeight) :=
  singular_flow_information
example : ∀ {N : ℕ} (f : Flow N), FlowCone f → ∀ u : ℕ → ℕ → ℝ,
    (∀ n k, k ≤ n → u (n+1) k+u (n+1) (k+1) = u n k) →
    (∑ n ∈ Finset.range (N+1), rawLayer f.stopWeight (fun n k => (n:ℝ)*u n k) n) =
      ∑ n ∈ Finset.range (N+1), rawLayer f.continueWeight u n := raw_stopping_depth


end Audit_genie_counterexample

namespace Audit_entropy_tail_bridge

open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile
example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (ρ B : ℝ),
    ThresholdHC.EntropyTail.selection μ ρ B = selectionValue μ ρ B :=
  ThresholdHC.EntropyTailBridge.canonical_selection_eq
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < B →
    ThresholdHC.EntropyTail.selection μ ρ B ≤ closedQuantileValue μ ρ B ∧
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (1+2*Real.sqrt 2) *
      ThresholdHC.EntropyTail.selection μ ρ B :=
  ThresholdHC.EntropyTailBridge.canonical_quantile_comparison

example : ThresholdHC.EntropyTail.SelectionBoundsStatement := ThresholdHC.EntropyTail.selection_bounds
example : ThresholdHC.EntropyTail.SingleAtomStatement := ThresholdHC.EntropyTail.single_atom
example : ThresholdHC.EntropyTail.SmallBudgetStatement := ThresholdHC.EntropyTail.small_budget
example : ThresholdHC.EntropyTail.EntropyTailNonvacuityStatement := ThresholdHC.EntropyTail.entropy_tail_nonvacuity
example : ThresholdHC.EntropyTail.HardSelectionStatement := ThresholdHC.EntropyTail.hard_selection
example : ThresholdHC.EntropyTail.EntropyTailUpperStatement := ThresholdHC.EntropyTailBridge.canonical_entropy_tail_upper

end Audit_entropy_tail_bridge

namespace Audit_assembly

open MeasureTheory Filter Set Real
open scoped ENNReal Topology BigOperators
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailAssembly
example : ∀ (ξ : Measure Gap) [IsFiniteMeasure ξ] (K : ℕ),
    (∑ k ∈ Finset.range (K+1), sqrt (eta ξ (4^k)*ordinaryCost ξ (4^k))) ≤
      208*(∫ d : Gap, min ((2:ℝ)^K) (d:ℝ)⁻¹ ∂ξ) := dyadic_kernel_sum
example : ∀ (ξ : Measure Gap) [IsFiniteMeasure ξ],
    (∑' k : ℕ, ENNReal.ofReal (sqrt (eta ξ (4^k)*ordinaryCost ξ (4^k)))) ≤
      ENNReal.ofReal 208*(∫⁻ d : Gap, ENNReal.ofReal ((d:ℝ)⁻¹) ∂ξ) := dyadic_kernel_tsum_extended
example : ∀ (σ : Measure Gap) [IsFiniteMeasure σ], measureCostEntropy σ < ⊤ →
    Tendsto (fun n => ∫ d : Gap, (d:ℝ)⁻¹ ∂σ.restrict {d : Gap | (d:ℝ) < bandEdge n})
      atTop (𝓝 0) := selectedRemainder_inverse_tendsto
example : ∀ (σ τ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ],
    Integrable (fun d : Gap => (d:ℝ)⁻¹^2) σ → Integrable (fun d : Gap => (d:ℝ)⁻¹) τ →
    ∀ (ρ Γ z : ℝ) (hρ : 0 < ρ), 0 ≤ Γ → 0 ≤ z →
    (∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) ≤ Γ → ρ/128 < (σ+τ).real univ →
    ∀ J : ℕ, z ≤ levelAccuracy ρ J/8 →
    (∑ l ∈ Finset.range (J+1), sqrt (17*levelAccuracy ρ l*
      adjacentCost (levelWorkCertificate σ τ ρ Γ z hρ) l)) ≤
      28000*(sqrt (ρ*Γ)+(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)) :=
  fun σ τ _ _ hσ hτ ρ Γ z hρ hΓ hz hA hm J hzJ =>
    multilevel_budget_certificate σ τ hσ hτ hρ hΓ hz hA hm J hzJ

end Audit_assembly

#print axioms ThresholdHC.CapIdentification.CapDeterminesTarget
#print axioms ThresholdHC.CapIdentification.CountMatch
#print axioms ThresholdHC.CapIdentification.MomentsDetermineTarget
#print axioms ThresholdHC.CapIdentification.OddMomentMatch
#print axioms ThresholdHC.CapIdentification.affine_bias_approximation
#print axioms ThresholdHC.CapIdentification.annihilates_prefix_iff
#print axioms ThresholdHC.CapIdentification.annihilates_prefixes_below
#print axioms ThresholdHC.CapIdentification.approximate_diameter_program_upper
#print axioms ThresholdHC.CapIdentification.arrayAt_const_mul
#print axioms ThresholdHC.CapIdentification.capDiameter
#print axioms ThresholdHC.CapIdentification.capDiameter_antitone
#print axioms ThresholdHC.CapIdentification.capDiameter_attained
#print axioms ThresholdHC.CapIdentification.capDiameter_bounds
#print axioms ThresholdHC.CapIdentification.capDiameter_program_floor
#print axioms ThresholdHC.CapIdentification.capDiameter_zero_iff_target
#print axioms ThresholdHC.CapIdentification.cap_threshold_equivalence
#print axioms ThresholdHC.CapIdentification.centeredPower
#print axioms ThresholdHC.CapIdentification.centeredPower_degree
#print axioms ThresholdHC.CapIdentification.centeredPower_eval_minus
#print axioms ThresholdHC.CapIdentification.centeredPower_eval_plus
#print axioms ThresholdHC.CapIdentification.centered_annihilation_iff
#print axioms ThresholdHC.CapIdentification.compact_affine_bias
#print axioms ThresholdHC.CapIdentification.compact_affine_recovery
#print axioms ThresholdHC.CapIdentification.constant_not_in_oddL2Span
#print axioms ThresholdHC.CapIdentification.constant_not_in_oddL2Span_infinite
#print axioms ThresholdHC.CapIdentification.constant_not_in_odd_span
#print axioms ThresholdHC.CapIdentification.countCoefficient_difference
#print axioms ThresholdHC.CapIdentification.countCoefficient_eq_iff_contrast
#print axioms ThresholdHC.CapIdentification.countCoefficient_le_choose
#print axioms ThresholdHC.CapIdentification.countCoefficient_polynomial
#print axioms ThresholdHC.CapIdentification.countEnvelope
#print axioms ThresholdHC.CapIdentification.countEnvelope_pos
#print axioms ThresholdHC.CapIdentification.countMean_eq_of_count_match
#print axioms ThresholdHC.CapIdentification.countMean_le_envelope
#print axioms ThresholdHC.CapIdentification.countMean_terminal
#print axioms ThresholdHC.CapIdentification.count_match_of_terminal
#print axioms ThresholdHC.CapIdentification.derivativeCore
#print axioms ThresholdHC.CapIdentification.derivativeCore_degree_le
#print axioms ThresholdHC.CapIdentification.exists_count_coefficients
#print axioms ThresholdHC.CapIdentification.exists_max_matching_gap
#print axioms ThresholdHC.CapIdentification.exists_odd_moment_contrast
#print axioms ThresholdHC.CapIdentification.exists_polynomial_moment_contrast
#print axioms ThresholdHC.CapIdentification.exists_prefix_coefficients
#print axioms ThresholdHC.CapIdentification.finite_moment_target_identified
#print axioms ThresholdHC.CapIdentification.finite_support_diameter_zero_iff
#print axioms ThresholdHC.CapIdentification.finite_support_target_of_moments
#print axioms ThresholdHC.CapIdentification.finite_support_target_threshold
#print axioms ThresholdHC.CapIdentification.finset_odd_interpolation
#print axioms ThresholdHC.CapIdentification.fixed_cap_identification
#print axioms ThresholdHC.CapIdentification.fullOutputFlow
#print axioms ThresholdHC.CapIdentification.fullOutputFlow_cone
#print axioms ThresholdHC.CapIdentification.fullOutputFlow_variance_bound
#print axioms ThresholdHC.CapIdentification.fullOutputFlow_work_bound
#print axioms ThresholdHC.CapIdentification.full_output_program_upper
#print axioms ThresholdHC.CapIdentification.functional_eq_coordinate_sum
#print axioms ThresholdHC.CapIdentification.gap_wordLikelihood
#print axioms ThresholdHC.CapIdentification.infinite_support_diameter_pos
#print axioms ThresholdHC.CapIdentification.infinite_support_program_floor
#print axioms ThresholdHC.CapIdentification.infinite_support_rare_indistinguishable
#print axioms ThresholdHC.CapIdentification.infinite_support_target_not_identified
#print axioms ThresholdHC.CapIdentification.informationRatio_pos_of_not_count_match
#print axioms ThresholdHC.CapIdentification.informationRatio_zero_iff_moments
#print axioms ThresholdHC.CapIdentification.informationRatio_zero_of_count_match
#print axioms ThresholdHC.CapIdentification.integrable_polynomial_probability
#print axioms ThresholdHC.CapIdentification.integrable_prefixLikelihood
#print axioms ThresholdHC.CapIdentification.integrable_sign_polynomial
#print axioms ThresholdHC.CapIdentification.integrable_weighted_prefix
#print axioms ThresholdHC.CapIdentification.liftTerminalOutput
#print axioms ThresholdHC.CapIdentification.matchingCoordinatePairs
#print axioms ThresholdHC.CapIdentification.matchingCoordinatePairs_compact
#print axioms ThresholdHC.CapIdentification.matchingCoordinatePairs_nonempty
#print axioms ThresholdHC.CapIdentification.matchingTargetGaps
#print axioms ThresholdHC.CapIdentification.matching_pair_certificate_floor
#print axioms ThresholdHC.CapIdentification.matching_pair_program_floor
#print axioms ThresholdHC.CapIdentification.matching_target_gap_le_twice_bias
#print axioms ThresholdHC.CapIdentification.mem_oddL2Span
#print axioms ThresholdHC.CapIdentification.momentCoordinates
#print axioms ThresholdHC.CapIdentification.momentCoordinates_match_iff
#print axioms ThresholdHC.CapIdentification.momentCoordinates_mem
#print axioms ThresholdHC.CapIdentification.momentCoordinates_none
#print axioms ThresholdHC.CapIdentification.momentCoordinates_some
#print axioms ThresholdHC.CapIdentification.momentPolynomial
#print axioms ThresholdHC.CapIdentification.moments_cap_threshold
#print axioms ThresholdHC.CapIdentification.moments_determine_target_iff
#print axioms ThresholdHC.CapIdentification.nullPolynomialMean
#print axioms ThresholdHC.CapIdentification.nullSignLaw
#print axioms ThresholdHC.CapIdentification.oddL2Span
#print axioms ThresholdHC.CapIdentification.oddL2Span_finite
#print axioms ThresholdHC.CapIdentification.oddMomentMatch_mono
#print axioms ThresholdHC.CapIdentification.oddMomentRepresentative
#print axioms ThresholdHC.CapIdentification.oddMomentRepresentative_degree
#print axioms ThresholdHC.CapIdentification.oddMomentRepresentative_difference
#print axioms ThresholdHC.CapIdentification.oddPolynomial
#print axioms ThresholdHC.CapIdentification.oddPolynomial_derivative_eval
#print axioms ThresholdHC.CapIdentification.oddPolynomial_eval
#print axioms ThresholdHC.CapIdentification.oddPolynomial_eval_zero
#print axioms ThresholdHC.CapIdentification.oddVector
#print axioms ThresholdHC.CapIdentification.odd_centered_prefix_equivalence
#print axioms ThresholdHC.CapIdentification.odd_interpolation
#print axioms ThresholdHC.CapIdentification.odd_level_card_le
#print axioms ThresholdHC.CapIdentification.odd_moments_iff_count_match
#print axioms ThresholdHC.CapIdentification.odd_moments_iff_prefix_contrast
#print axioms ThresholdHC.CapIdentification.original_wordLikelihood_integral
#print axioms ThresholdHC.CapIdentification.outputSquareSum
#print axioms ThresholdHC.CapIdentification.outputSquareSum_ge
#print axioms ThresholdHC.CapIdentification.outputSquareSum_nonneg
#print axioms ThresholdHC.CapIdentification.perspective_strict_pos
#print axioms ThresholdHC.CapIdentification.perspective_zero_left
#print axioms ThresholdHC.CapIdentification.polynomialL2
#print axioms ThresholdHC.CapIdentification.polynomialL2_ae
#print axioms ThresholdHC.CapIdentification.polynomialL2_inner
#print axioms ThresholdHC.CapIdentification.polynomialL2_odd
#print axioms ThresholdHC.CapIdentification.polynomialMomentSet
#print axioms ThresholdHC.CapIdentification.polynomialMomentSet_compact_convex
#print axioms ThresholdHC.CapIdentification.polynomialMomentSet_coordinates
#print axioms ThresholdHC.CapIdentification.polynomialMomentSet_eq_rareMomentSet
#print axioms ThresholdHC.CapIdentification.polynomial_gap_bound
#print axioms ThresholdHC.CapIdentification.polynomial_gap_memLp
#print axioms ThresholdHC.CapIdentification.polynomial_mem_prefix_span
#print axioms ThresholdHC.CapIdentification.polynomial_moment_difference
#print axioms ThresholdHC.CapIdentification.populationPolynomialMean
#print axioms ThresholdHC.CapIdentification.populationPolynomialMean_odd
#print axioms ThresholdHC.CapIdentification.populationPolynomialMean_prefix
#print axioms ThresholdHC.CapIdentification.positive_square_injective
#print axioms ThresholdHC.CapIdentification.prefixLikelihood_le_one
#print axioms ThresholdHC.CapIdentification.prefixPolynomial
#print axioms ThresholdHC.CapIdentification.prefixPolynomial_degree
#print axioms ThresholdHC.CapIdentification.prefixPolynomial_diagonal
#print axioms ThresholdHC.CapIdentification.prefixPolynomial_elevation
#print axioms ThresholdHC.CapIdentification.prefixPolynomial_eval_minus
#print axioms ThresholdHC.CapIdentification.prefixPolynomial_eval_plus
#print axioms ThresholdHC.CapIdentification.programSquared_budget_limit
#print axioms ThresholdHC.CapIdentification.programValue_budget_limit
#print axioms ThresholdHC.CapIdentification.rare_indistinguishable_of_large_support
#print axioms ThresholdHC.CapIdentification.rare_indistinguishable_of_not_in_span
#print axioms ThresholdHC.CapIdentification.rare_priors_of_bounded_contrast
#print axioms ThresholdHC.CapIdentification.signContrast
#print axioms ThresholdHC.CapIdentification.signContrast_apply
#print axioms ThresholdHC.CapIdentification.signContrast_even
#print axioms ThresholdHC.CapIdentification.signContrast_odd
#print axioms ThresholdHC.CapIdentification.signDifference_norm
#print axioms ThresholdHC.CapIdentification.stopped_law_eq_of_odd_moments
#print axioms ThresholdHC.CapIdentification.sum_terminal
#print axioms ThresholdHC.CapIdentification.terminalArray
#print axioms ThresholdHC.CapIdentification.terminal_polynomial_representation
#print axioms ThresholdHC.CapIdentification.topState
#print axioms ThresholdHC.CapIdentification.weightedPolynomialIntegral
#print axioms ThresholdHC.CapIdentification.wordLikelihood_eq_of_count_match
#print axioms ThresholdHC.EntropyTail.EntropyTailLawStatement
#print axioms ThresholdHC.EntropyTail.EntropyTailLowerStatement
#print axioms ThresholdHC.EntropyTail.EntropyTailNonvacuityStatement
#print axioms ThresholdHC.EntropyTail.EntropyTailUpperStatement
#print axioms ThresholdHC.EntropyTail.HardSelectionStatement
#print axioms ThresholdHC.EntropyTail.SelectionBoundsStatement
#print axioms ThresholdHC.EntropyTail.SingleAtomStatement
#print axioms ThresholdHC.EntropyTail.SmallBudgetStatement
#print axioms ThresholdHC.EntropyTail.band
#print axioms ThresholdHC.EntropyTail.bandCost
#print axioms ThresholdHC.EntropyTail.bandCost_dirac
#print axioms ThresholdHC.EntropyTail.bandCost_mono
#print axioms ThresholdHC.EntropyTail.bandCost_ne_top
#print axioms ThresholdHC.EntropyTail.bandCost_sum_smul
#print axioms ThresholdHC.EntropyTail.band_disjoint
#print axioms ThresholdHC.EntropyTail.costEntropy
#print axioms ThresholdHC.EntropyTail.costEntropy_add
#print axioms ThresholdHC.EntropyTail.costEntropy_eq_sum
#print axioms ThresholdHC.EntropyTail.costEntropy_mono
#print axioms ThresholdHC.EntropyTail.costEntropy_nonneg
#print axioms ThresholdHC.EntropyTail.costEntropy_prefix_le_succ
#print axioms ThresholdHC.EntropyTail.costEntropy_smul
#print axioms ThresholdHC.EntropyTail.entropyTerm_ofReal
#print axioms ThresholdHC.EntropyTail.entropy_tail_nonvacuity
#print axioms ThresholdHC.EntropyTail.eq_smul_dirac_of_le
#print axioms ThresholdHC.EntropyTail.exists_band
#print axioms ThresholdHC.EntropyTail.four_le_inv_sq
#print axioms ThresholdHC.EntropyTail.four_mass_le_gamma
#print axioms ThresholdHC.EntropyTail.gamma
#print axioms ThresholdHC.EntropyTail.gamma_dirac_le
#print axioms ThresholdHC.EntropyTail.gamma_eq_iSup
#print axioms ThresholdHC.EntropyTail.gamma_mono
#print axioms ThresholdHC.EntropyTail.gamma_zero
#print axioms ThresholdHC.EntropyTail.hard_le_objective_add
#print axioms ThresholdHC.EntropyTail.hard_selection
#print axioms ThresholdHC.EntropyTail.iInf_objective_lower
#print axioms ThresholdHC.EntropyTail.layer
#print axioms ThresholdHC.EntropyTail.layerDensity
#print axioms ThresholdHC.EntropyTail.layerDensity_bounds
#print axioms ThresholdHC.EntropyTail.layerMixture
#print axioms ThresholdHC.EntropyTail.lintegral_layerMixture
#print axioms ThresholdHC.EntropyTail.lintegral_le_gamma
#print axioms ThresholdHC.EntropyTail.logsum_two
#print axioms ThresholdHC.EntropyTail.measurableSet_band
#print axioms ThresholdHC.EntropyTail.measurableSet_layer
#print axioms ThresholdHC.EntropyTail.measurable_layerDensity
#print axioms ThresholdHC.EntropyTail.measurable_tailWeight
#print axioms ThresholdHC.EntropyTail.objective_eq_ofReal
#print axioms ThresholdHC.EntropyTail.objective_lower
#print axioms ThresholdHC.EntropyTail.ofReal_prefixEntropy_le_gamma
#print axioms ThresholdHC.EntropyTail.prefixEntropy
#print axioms ThresholdHC.EntropyTail.prefixEntropy_mono
#print axioms ThresholdHC.EntropyTail.prefixEntropy_nonneg
#print axioms ThresholdHC.EntropyTail.selection
#print axioms ThresholdHC.EntropyTail.selectionObjective
#print axioms ThresholdHC.EntropyTail.selectionObjective_self
#print axioms ThresholdHC.EntropyTail.selectionObjective_zero
#print axioms ThresholdHC.EntropyTail.selection_bounds
#print axioms ThresholdHC.EntropyTail.selection_le_objective
#print axioms ThresholdHC.EntropyTail.selection_le_rho
#print axioms ThresholdHC.EntropyTail.single_atom
#print axioms ThresholdHC.EntropyTail.single_lower
#print axioms ThresholdHC.EntropyTail.small_budget
#print axioms ThresholdHC.EntropyTail.sum_bandCost_le_gamma
#print axioms ThresholdHC.EntropyTail.sum_le_costEntropy
#print axioms ThresholdHC.EntropyTail.sum_mul_sqrt_le
#print axioms ThresholdHC.EntropyTail.sum_smul_costEntropy_le
#print axioms ThresholdHC.EntropyTail.sum_smul_gamma_le
#print axioms ThresholdHC.EntropyTail.tailCost
#print axioms ThresholdHC.EntropyTail.tailCost_dirac
#print axioms ThresholdHC.EntropyTail.tailCost_le_mass
#print axioms ThresholdHC.EntropyTail.tailCost_lower
#print axioms ThresholdHC.EntropyTail.tailCost_smul
#print axioms ThresholdHC.EntropyTail.tailCost_sub_add
#print axioms ThresholdHC.EntropyTail.tailCost_sum_smul
#print axioms ThresholdHC.EntropyTail.tailCost_zero
#print axioms ThresholdHC.EntropyTailAssembly.adjacentCost
#print axioms ThresholdHC.EntropyTailAssembly.adjacent_root_level
#print axioms ThresholdHC.EntropyTailAssembly.adjacent_root_sum
#print axioms ThresholdHC.EntropyTailAssembly.ae_finite_band_cover
#print axioms ThresholdHC.EntropyTailAssembly.bandCost_hasSum
#print axioms ThresholdHC.EntropyTailAssembly.bandCost_zero_measure
#print axioms ThresholdHC.EntropyTailAssembly.bandEdge_tendsto_zero
#print axioms ThresholdHC.EntropyTailAssembly.bandWeights
#print axioms ThresholdHC.EntropyTailAssembly.bandWeights_coe
#print axioms ThresholdHC.EntropyTailAssembly.bandWeights_entropy
#print axioms ThresholdHC.EntropyTailAssembly.bandWeights_le_one
#print axioms ThresholdHC.EntropyTailAssembly.bandWeights_log
#print axioms ThresholdHC.EntropyTailAssembly.bandWeights_positive
#print axioms ThresholdHC.EntropyTailAssembly.bandWeights_probability
#print axioms ThresholdHC.EntropyTailAssembly.band_inverse_bound
#print axioms ThresholdHC.EntropyTailAssembly.band_large_log
#print axioms ThresholdHC.EntropyTailAssembly.band_large_scaledKernel
#print axioms ThresholdHC.EntropyTailAssembly.band_scale_le_inverse
#print axioms ThresholdHC.EntropyTailAssembly.band_scaled_gap_le_one
#print axioms ThresholdHC.EntropyTailAssembly.bank_level_error
#print axioms ThresholdHC.EntropyTailAssembly.bank_mixture_work_bound
#print axioms ThresholdHC.EntropyTailAssembly.cap_dichotomy
#print axioms ThresholdHC.EntropyTailAssembly.cap_twice
#print axioms ThresholdHC.EntropyTailAssembly.conditionalRaceWork
#print axioms ThresholdHC.EntropyTailAssembly.conditionalRaceWork_le_cap
#print axioms ThresholdHC.EntropyTailAssembly.conditionalRaceWork_nonneg
#print axioms ThresholdHC.EntropyTailAssembly.dyadic_kernel_finset_inverse
#print axioms ThresholdHC.EntropyTailAssembly.dyadic_kernel_sum
#print axioms ThresholdHC.EntropyTailAssembly.dyadic_kernel_sum_extended
#print axioms ThresholdHC.EntropyTailAssembly.dyadic_kernel_sum_inverse
#print axioms ThresholdHC.EntropyTailAssembly.dyadic_kernel_tsum_extended
#print axioms ThresholdHC.EntropyTailAssembly.dyadic_power_sum
#print axioms ThresholdHC.EntropyTailAssembly.errorCapExponent
#print axioms ThresholdHC.EntropyTailAssembly.errorCapExponent_error_lower
#print axioms ThresholdHC.EntropyTailAssembly.errorCapExponent_gt_one
#print axioms ThresholdHC.EntropyTailAssembly.errorCapExponent_min
#print axioms ThresholdHC.EntropyTailAssembly.errorCapExponent_spec
#print axioms ThresholdHC.EntropyTailAssembly.errorCapExponent_strict
#print axioms ThresholdHC.EntropyTailAssembly.eta
#print axioms ThresholdHC.EntropyTailAssembly.eta_add
#print axioms ThresholdHC.EntropyTailAssembly.eta_antitone
#print axioms ThresholdHC.EntropyTailAssembly.eta_four
#print axioms ThresholdHC.EntropyTailAssembly.eta_four_mul
#print axioms ThresholdHC.EntropyTailAssembly.eta_le_inverse
#print axioms ThresholdHC.EntropyTailAssembly.eta_le_inverseSquare
#print axioms ThresholdHC.EntropyTailAssembly.eta_le_mass
#print axioms ThresholdHC.EntropyTailAssembly.eta_nonneg
#print axioms ThresholdHC.EntropyTailAssembly.eta_tendsto
#print axioms ThresholdHC.EntropyTailAssembly.exists_error_cap
#print axioms ThresholdHC.EntropyTailAssembly.exists_terminal_level
#print axioms ThresholdHC.EntropyTailAssembly.four_pow_eq_two
#print axioms ThresholdHC.EntropyTailAssembly.fourthRoot_levelAccuracy
#print axioms ThresholdHC.EntropyTailAssembly.half_geometric_tail_sum
#print axioms ThresholdHC.EntropyTailAssembly.hasSum_dyadic_cubic_tail
#print axioms ThresholdHC.EntropyTailAssembly.hasSum_dyadic_linear_tail
#print axioms ThresholdHC.EntropyTailAssembly.integrable_mixtureRaceWork
#print axioms ThresholdHC.EntropyTailAssembly.integrable_ordinaryWorkKernel
#print axioms ThresholdHC.EntropyTailAssembly.integrable_scaledKernel
#print axioms ThresholdHC.EntropyTailAssembly.integrable_signLaw
#print axioms ThresholdHC.EntropyTailAssembly.integrable_truncated_inverse
#print axioms ThresholdHC.EntropyTailAssembly.integral_eq_sum_bands
#print axioms ThresholdHC.EntropyTailAssembly.integrated_log_surcharge
#print axioms ThresholdHC.EntropyTailAssembly.integrated_raceWork_le_cap
#print axioms ThresholdHC.EntropyTailAssembly.integrated_raceWork_le_ordinary
#print axioms ThresholdHC.EntropyTailAssembly.inverseSquare_eq_band_total
#print axioms ThresholdHC.EntropyTailAssembly.inverseSquare_integrable_of_entropy
#print axioms ThresholdHC.EntropyTailAssembly.inverseSquare_integrable_of_support
#print axioms ThresholdHC.EntropyTailAssembly.inverseSquare_zero_measure
#print axioms ThresholdHC.EntropyTailAssembly.inverse_integrable_of_entropy
#print axioms ThresholdHC.EntropyTailAssembly.large_envelope_sum
#print axioms ThresholdHC.EntropyTailAssembly.levelAccuracy
#print axioms ThresholdHC.EntropyTailAssembly.levelAccuracy_le_first
#print axioms ThresholdHC.EntropyTailAssembly.levelAccuracy_pos
#print axioms ThresholdHC.EntropyTailAssembly.levelAccuracy_succ
#print axioms ThresholdHC.EntropyTailAssembly.levelAccuracy_tendsto
#print axioms ThresholdHC.EntropyTailAssembly.levelAccuracy_zero
#print axioms ThresholdHC.EntropyTailAssembly.levelEpsilon
#print axioms ThresholdHC.EntropyTailAssembly.levelEpsilon_accuracy
#print axioms ThresholdHC.EntropyTailAssembly.levelEpsilon_le_one
#print axioms ThresholdHC.EntropyTailAssembly.levelEpsilon_log
#print axioms ThresholdHC.EntropyTailAssembly.levelEpsilon_pos
#print axioms ThresholdHC.EntropyTailAssembly.levelWorkCertificate
#print axioms ThresholdHC.EntropyTailAssembly.levelWorkCertificate_nonneg
#print axioms ThresholdHC.EntropyTailAssembly.levelWorkCertificate_root_sum
#print axioms ThresholdHC.EntropyTailAssembly.level_work_root
#print axioms ThresholdHC.EntropyTailAssembly.log_inverse_product
#print axioms ThresholdHC.EntropyTailAssembly.measurable_conditionalRaceWork
#print axioms ThresholdHC.EntropyTailAssembly.measurable_mixtureRaceWork
#print axioms ThresholdHC.EntropyTailAssembly.min_one_sq_le
#print axioms ThresholdHC.EntropyTailAssembly.mixed_level_envelope
#print axioms ThresholdHC.EntropyTailAssembly.mixed_scalar_bound
#print axioms ThresholdHC.EntropyTailAssembly.mixed_work_sum
#print axioms ThresholdHC.EntropyTailAssembly.mixtureRaceWork
#print axioms ThresholdHC.EntropyTailAssembly.mixtureRaceWork_le_cap
#print axioms ThresholdHC.EntropyTailAssembly.mixtureRaceWork_le_ordinary
#print axioms ThresholdHC.EntropyTailAssembly.mixtureRaceWork_nonneg
#print axioms ThresholdHC.EntropyTailAssembly.multilevel_budget_certificate
#print axioms ThresholdHC.EntropyTailAssembly.ordinaryCost
#print axioms ThresholdHC.EntropyTailAssembly.ordinaryCost_add
#print axioms ThresholdHC.EntropyTailAssembly.ordinaryCost_le_cap
#print axioms ThresholdHC.EntropyTailAssembly.ordinaryCost_le_inverse
#print axioms ThresholdHC.EntropyTailAssembly.ordinaryCost_nonneg
#print axioms ThresholdHC.EntropyTailAssembly.ordinaryErrorKernel_antitone
#print axioms ThresholdHC.EntropyTailAssembly.ordinaryErrorKernel_four
#print axioms ThresholdHC.EntropyTailAssembly.ordinaryErrorKernel_four_mul
#print axioms ThresholdHC.EntropyTailAssembly.ordinaryErrorKernel_le_inverse
#print axioms ThresholdHC.EntropyTailAssembly.ordinaryErrorKernel_le_inverseSquare
#print axioms ThresholdHC.EntropyTailAssembly.ordinaryErrorKernel_nonneg
#print axioms ThresholdHC.EntropyTailAssembly.ordinaryErrorKernel_tendsto
#print axioms ThresholdHC.EntropyTailAssembly.ordinaryWorkKernel_le_inverse
#print axioms ThresholdHC.EntropyTailAssembly.ordinaryWorkKernel_nonneg
#print axioms ThresholdHC.EntropyTailAssembly.quarter_geometric_sum
#print axioms ThresholdHC.EntropyTailAssembly.quarter_linear_sum
#print axioms ThresholdHC.EntropyTailAssembly.quarter_linear_term
#print axioms ThresholdHC.EntropyTailAssembly.quarter_tail_sum
#print axioms ThresholdHC.EntropyTailAssembly.referenceWeights
#print axioms ThresholdHC.EntropyTailAssembly.referenceWeights_probability
#print axioms ThresholdHC.EntropyTailAssembly.scaledKernel
#print axioms ThresholdHC.EntropyTailAssembly.scaledKernel_le_cap
#print axioms ThresholdHC.EntropyTailAssembly.scaledKernel_nonneg
#print axioms ThresholdHC.EntropyTailAssembly.scaledKernel_sum
#print axioms ThresholdHC.EntropyTailAssembly.scaledKernel_sum_band
#print axioms ThresholdHC.EntropyTailAssembly.schedule_caps_strict
#print axioms ThresholdHC.EntropyTailAssembly.selectedRemainder
#print axioms ThresholdHC.EntropyTailAssembly.selectedRemainder_finite
#print axioms ThresholdHC.EntropyTailAssembly.selectedRemainder_inverse_tendsto
#print axioms ThresholdHC.EntropyTailAssembly.selectedRemainder_le
#print axioms ThresholdHC.EntropyTailAssembly.selectedTruncation
#print axioms ThresholdHC.EntropyTailAssembly.selectedTruncation_add_remainder
#print axioms ThresholdHC.EntropyTailAssembly.selectedTruncation_entropy_finite
#print axioms ThresholdHC.EntropyTailAssembly.selectedTruncation_entropy_le
#print axioms ThresholdHC.EntropyTailAssembly.selectedTruncation_finite
#print axioms ThresholdHC.EntropyTailAssembly.selectedTruncation_le
#print axioms ThresholdHC.EntropyTailAssembly.selectedTruncation_support
#print axioms ThresholdHC.EntropyTailAssembly.selected_inverseSquare_pos
#print axioms ThresholdHC.EntropyTailAssembly.selected_level_work
#print axioms ThresholdHC.EntropyTailAssembly.selected_signMean_le
#print axioms ThresholdHC.EntropyTailAssembly.selected_work_bound
#print axioms ThresholdHC.EntropyTailAssembly.sqrt_accuracy_ratio
#print axioms ThresholdHC.EntropyTailAssembly.sqrt_add_subadditive
#print axioms ThresholdHC.EntropyTailAssembly.sqrt_kernel_le_scaled
#print axioms ThresholdHC.EntropyTailAssembly.sqrt_levelAccuracy
#print axioms ThresholdHC.EntropyTailAssembly.sqrt_levelAccuracy_half
#print axioms ThresholdHC.EntropyTailAssembly.terminal_ratio_sum
#print axioms ThresholdHC.EntropyTailAssembly.terminal_selected_work
#print axioms ThresholdHC.EntropyTailAssembly.terminal_sqrt_ratio
#print axioms ThresholdHC.EntropyTailAssembly.three_piece_level_work
#print axioms ThresholdHC.EntropyTailAssembly.unresolved_level_envelope
#print axioms ThresholdHC.EntropyTailAssembly.unresolved_work_sum
#print axioms ThresholdHC.EntropyTailAssembly.weighted_log_surcharge_pointwise
#print axioms ThresholdHC.EntropyTailBridge.canonical_bandCost_eq
#print axioms ThresholdHC.EntropyTailBridge.canonical_band_eq
#print axioms ThresholdHC.EntropyTailBridge.canonical_costEntropy_eq
#print axioms ThresholdHC.EntropyTailBridge.canonical_entropy_tail_upper
#print axioms ThresholdHC.EntropyTailBridge.canonical_gamma_eq
#print axioms ThresholdHC.EntropyTailBridge.canonical_quantile_comparison
#print axioms ThresholdHC.EntropyTailBridge.canonical_selectionObjective_eq
#print axioms ThresholdHC.EntropyTailBridge.canonical_selection_eq
#print axioms ThresholdHC.EntropyTailBridge.canonical_tailCost_eq
#print axioms ThresholdHC.EntropyTailExecution.FiniteCall
#print axioms ThresholdHC.EntropyTailExecution.PlanConsumes
#print axioms ThresholdHC.EntropyTailExecution.PlanConsumes.append
#print axioms ThresholdHC.EntropyTailExecution.PlanConsumes.path_eq
#print axioms ThresholdHC.EntropyTailExecution.PlanConsumes.state_eq
#print axioms ThresholdHC.EntropyTailExecution.PlanState
#print axioms ThresholdHC.EntropyTailExecution.allocatedEstimator
#print axioms ThresholdHC.EntropyTailExecution.allocated_mse_bound
#print axioms ThresholdHC.EntropyTailExecution.allocated_rootRisk_bound
#print axioms ThresholdHC.EntropyTailExecution.allocated_work_bound
#print axioms ThresholdHC.EntropyTailExecution.allocationRates
#print axioms ThresholdHC.EntropyTailExecution.allocationRates_coe
#print axioms ThresholdHC.EntropyTailExecution.allocationRates_pos
#print axioms ThresholdHC.EntropyTailExecution.bankFamily
#print axioms ThresholdHC.EntropyTailExecution.bankFamilyCap
#print axioms ThresholdHC.EntropyTailExecution.bankFamily_bias
#print axioms ThresholdHC.EntropyTailExecution.bankFamily_binary
#print axioms ThresholdHC.EntropyTailExecution.bankFamily_cost_bound
#print axioms ThresholdHC.EntropyTailExecution.bankFamily_second
#print axioms ThresholdHC.EntropyTailExecution.bankFamily_work
#print axioms ThresholdHC.EntropyTailExecution.callWord
#print axioms ThresholdHC.EntropyTailExecution.call_cost_integrable
#print axioms ThresholdHC.EntropyTailExecution.call_cost_mean_ge_one
#print axioms ThresholdHC.EntropyTailExecution.closed_quantile_upper
#print axioms ThresholdHC.EntropyTailExecution.closed_quantile_upper_30001
#print axioms ThresholdHC.EntropyTailExecution.consumes_call
#print axioms ThresholdHC.EntropyTailExecution.consumes_call_prefix
#print axioms ThresholdHC.EntropyTailExecution.countLabel_injective
#print axioms ThresholdHC.EntropyTailExecution.countLabels
#print axioms ThresholdHC.EntropyTailExecution.countLabels_nodup
#print axioms ThresholdHC.EntropyTailExecution.countLaw
#print axioms ThresholdHC.EntropyTailExecution.countLaw_probability
#print axioms ThresholdHC.EntropyTailExecution.differenceCall
#print axioms ThresholdHC.EntropyTailExecution.entropy_tail_upper
#print axioms ThresholdHC.EntropyTailExecution.entropy_tail_upper_28000
#print axioms ThresholdHC.EntropyTailExecution.finitePlanEstimator
#print axioms ThresholdHC.EntropyTailExecution.finitePlanHaltTime
#print axioms ThresholdHC.EntropyTailExecution.finitePlanOutput
#print axioms ThresholdHC.EntropyTailExecution.finitePlanOutput_at_halt
#print axioms ThresholdHC.EntropyTailExecution.finitePlanPolicy
#print axioms ThresholdHC.EntropyTailExecution.finitePlan_expectedWork
#print axioms ThresholdHC.EntropyTailExecution.finitePlan_path_eq
#print axioms ThresholdHC.EntropyTailExecution.finitePlan_population_output
#print axioms ThresholdHC.EntropyTailExecution.finitePlan_population_work
#print axioms ThresholdHC.EntropyTailExecution.finitePlan_squaredRisk
#print axioms ThresholdHC.EntropyTailExecution.finite_entropy_three_piece
#print axioms ThresholdHC.EntropyTailExecution.finite_level_minimax
#print axioms ThresholdHC.EntropyTailExecution.finite_support_three_piece
#print axioms ThresholdHC.EntropyTailExecution.full_plan_consumes
#print axioms ThresholdHC.EntropyTailExecution.incrementCall
#print axioms ThresholdHC.EntropyTailExecution.incrementCall_bounded
#print axioms ThresholdHC.EntropyTailExecution.incrementCall_cost_bound
#print axioms ThresholdHC.EntropyTailExecution.incrementCall_cost_le
#print axioms ThresholdHC.EntropyTailExecution.incrementCall_integrable
#print axioms ThresholdHC.EntropyTailExecution.incrementCall_mean_sum
#print axioms ThresholdHC.EntropyTailExecution.incrementCall_second_bound
#print axioms ThresholdHC.EntropyTailExecution.incrementCall_value
#print axioms ThresholdHC.EntropyTailExecution.incrementCall_work_bound
#print axioms ThresholdHC.EntropyTailExecution.indexedCall
#print axioms ThresholdHC.EntropyTailExecution.indexedCall_pair
#print axioms ThresholdHC.EntropyTailExecution.initialPlan
#print axioms ThresholdHC.EntropyTailExecution.levelAccuracy_antitone
#print axioms ThresholdHC.EntropyTailExecution.measurable_finitePlanHaltTime
#print axioms ThresholdHC.EntropyTailExecution.measurable_finitePlanOutput
#print axioms ThresholdHC.EntropyTailExecution.minimax_half_rarity
#print axioms ThresholdHC.EntropyTailExecution.minimax_le_selectionCost
#print axioms ThresholdHC.EntropyTailExecution.observedDone
#print axioms ThresholdHC.EntropyTailExecution.observedDone_word
#print axioms ThresholdHC.EntropyTailExecution.observedValue_word
#print axioms ThresholdHC.EntropyTailExecution.pairedStreams
#print axioms ThresholdHC.EntropyTailExecution.pairedStreams_preserving
#print axioms ThresholdHC.EntropyTailExecution.planLabel
#print axioms ThresholdHC.EntropyTailExecution.planRecords
#print axioms ThresholdHC.EntropyTailExecution.planRecords_output
#print axioms ThresholdHC.EntropyTailExecution.planRun
#print axioms ThresholdHC.EntropyTailExecution.planRun_absorbs
#print axioms ThresholdHC.EntropyTailExecution.planRun_append
#print axioms ThresholdHC.EntropyTailExecution.planRun_call_complete
#print axioms ThresholdHC.EntropyTailExecution.planRun_call_partial
#print axioms ThresholdHC.EntropyTailExecution.planStateMeasurableSpace
#print axioms ThresholdHC.EntropyTailExecution.planStateOutput
#print axioms ThresholdHC.EntropyTailExecution.planStep
#print axioms ThresholdHC.EntropyTailExecution.planWord
#print axioms ThresholdHC.EntropyTailExecution.planWord_length
#print axioms ThresholdHC.EntropyTailExecution.plannedCost
#print axioms ThresholdHC.EntropyTailExecution.plannedCost_counts
#print axioms ThresholdHC.EntropyTailExecution.plannedValue
#print axioms ThresholdHC.EntropyTailExecution.plannedValue_counts
#print axioms ThresholdHC.EntropyTailExecution.poissonPlanEstimator
#print axioms ThresholdHC.EntropyTailExecution.poissonPlanInput
#print axioms ThresholdHC.EntropyTailExecution.poissonPlanInput_preserving
#print axioms ThresholdHC.EntropyTailExecution.poissonPlan_expectedWork
#print axioms ThresholdHC.EntropyTailExecution.poissonPlan_squaredRisk
#print axioms ThresholdHC.EntropyTailExecution.resolved_mass_large
#print axioms ThresholdHC.EntropyTailExecution.scaleCall
#print axioms ThresholdHC.EntropyTailExecution.scheduledCall
#print axioms ThresholdHC.EntropyTailExecution.statePolicy
#print axioms ThresholdHC.EntropyTailExecution.sum_countLabels
#print axioms ThresholdHC.EntropyTailQuantile.ClosedQuantileUpperStatement
#print axioms ThresholdHC.EntropyTailQuantile.EntropyTailUpperStatement
#print axioms ThresholdHC.EntropyTailQuantile.QuantileComparisonStatement
#print axioms ThresholdHC.EntropyTailQuantile.QuantileSplitStatement
#print axioms ThresholdHC.EntropyTailQuantile.band
#print axioms ThresholdHC.EntropyTailQuantile.bandCost
#print axioms ThresholdHC.EntropyTailQuantile.bandCost_add
#print axioms ThresholdHC.EntropyTailQuantile.bandCost_eq_zero_of_support
#print axioms ThresholdHC.EntropyTailQuantile.bandCost_mono
#print axioms ThresholdHC.EntropyTailQuantile.bandCost_nonneg
#print axioms ThresholdHC.EntropyTailQuantile.bandEdge
#print axioms ThresholdHC.EntropyTailQuantile.bandEdge_antitone
#print axioms ThresholdHC.EntropyTailQuantile.bandEdge_pos
#print axioms ThresholdHC.EntropyTailQuantile.bandEdge_succ
#print axioms ThresholdHC.EntropyTailQuantile.band_inverseSquare_integrable
#print axioms ThresholdHC.EntropyTailQuantile.bands_disjoint
#print axioms ThresholdHC.EntropyTailQuantile.binary_entropy_le
#print axioms ThresholdHC.EntropyTailQuantile.budgetScale
#print axioms ThresholdHC.EntropyTailQuantile.budgetScale_nonneg
#print axioms ThresholdHC.EntropyTailQuantile.budgetScale_pos
#print axioms ThresholdHC.EntropyTailQuantile.closedQuantileValue
#print axioms ThresholdHC.EntropyTailQuantile.continuous_costEntropy
#print axioms ThresholdHC.EntropyTailQuantile.costEntropy
#print axioms ThresholdHC.EntropyTailQuantile.costEntropy_add_le
#print axioms ThresholdHC.EntropyTailQuantile.costEntropy_add_le_two
#print axioms ThresholdHC.EntropyTailQuantile.costEntropy_eq_log_sum
#print axioms ThresholdHC.EntropyTailQuantile.costEntropy_le_reference
#print axioms ThresholdHC.EntropyTailQuantile.costEntropy_mono
#print axioms ThresholdHC.EntropyTailQuantile.costEntropy_nonneg
#print axioms ThresholdHC.EntropyTailQuantile.costEntropy_normalized
#print axioms ThresholdHC.EntropyTailQuantile.costEntropy_prefix_eq_of_eventually_zero
#print axioms ThresholdHC.EntropyTailQuantile.costEntropy_prefix_le_of_eventually_zero
#print axioms ThresholdHC.EntropyTailQuantile.costEntropy_prefix_monotone
#print axioms ThresholdHC.EntropyTailQuantile.costEntropy_prefix_succ
#print axioms ThresholdHC.EntropyTailQuantile.costEntropy_smul
#print axioms ThresholdHC.EntropyTailQuantile.costEntropy_superadditive
#print axioms ThresholdHC.EntropyTailQuantile.costEntropy_zero
#print axioms ThresholdHC.EntropyTailQuantile.costTotal
#print axioms ThresholdHC.EntropyTailQuantile.costTotal_add
#print axioms ThresholdHC.EntropyTailQuantile.costTotal_le_costEntropy
#print axioms ThresholdHC.EntropyTailQuantile.costTotal_nonneg
#print axioms ThresholdHC.EntropyTailQuantile.costTotal_smul
#print axioms ThresholdHC.EntropyTailQuantile.costTotal_zero
#print axioms ThresholdHC.EntropyTailQuantile.dyadic_reference_coefficient
#print axioms ThresholdHC.EntropyTailQuantile.dyadic_reference_sum
#print axioms ThresholdHC.EntropyTailQuantile.dyadic_reference_sum_le_one
#print axioms ThresholdHC.EntropyTailQuantile.entropy_root_eq_ofReal
#print axioms ThresholdHC.EntropyTailQuantile.eq_zero_of_costTotal_eq_zero
#print axioms ThresholdHC.EntropyTailQuantile.exists_band_cutoff
#print axioms ThresholdHC.EntropyTailQuantile.gapCDF
#print axioms ThresholdHC.EntropyTailQuantile.gapCDF_eq
#print axioms ThresholdHC.EntropyTailQuantile.gapCDF_half
#print axioms ThresholdHC.EntropyTailQuantile.gapCDF_zero
#print axioms ThresholdHC.EntropyTailQuantile.gap_mass_le_eq
#print axioms ThresholdHC.EntropyTailQuantile.homogeneous_negMulLog_add
#print axioms ThresholdHC.EntropyTailQuantile.iUnion_band
#print axioms ThresholdHC.EntropyTailQuantile.inverseSquare_lintegral_le_entropy
#print axioms ThresholdHC.EntropyTailQuantile.inverse_integrable_of_support
#print axioms ThresholdHC.EntropyTailQuantile.inverse_lintegral_le_sqrt_moment
#print axioms ThresholdHC.EntropyTailQuantile.le_costTotal
#print axioms ThresholdHC.EntropyTailQuantile.levelThreshold
#print axioms ThresholdHC.EntropyTailQuantile.lowerCut
#print axioms ThresholdHC.EntropyTailQuantile.lowerCut_add
#print axioms ThresholdHC.EntropyTailQuantile.lowerCut_add_upperCut
#print axioms ThresholdHC.EntropyTailQuantile.lowerCut_le
#print axioms ThresholdHC.EntropyTailQuantile.lowerCut_mono
#print axioms ThresholdHC.EntropyTailQuantile.measurableSet_band
#print axioms ThresholdHC.EntropyTailQuantile.measureCostEntropy
#print axioms ThresholdHC.EntropyTailQuantile.measureCostEntropy_add_le_two
#print axioms ThresholdHC.EntropyTailQuantile.measureCostEntropy_eq_prefix_of_support
#print axioms ThresholdHC.EntropyTailQuantile.measureCostEntropy_lt_top_of_support
#print axioms ThresholdHC.EntropyTailQuantile.measureCostEntropy_mono
#print axioms ThresholdHC.EntropyTailQuantile.negMulLog_add_le
#print axioms ThresholdHC.EntropyTailQuantile.quantileBoundaryFraction
#print axioms ThresholdHC.EntropyTailQuantile.quantileBoundaryFraction_properties
#print axioms ThresholdHC.EntropyTailQuantile.quantileCore
#print axioms ThresholdHC.EntropyTailQuantile.quantileCore_entropy_bound
#print axioms ThresholdHC.EntropyTailQuantile.quantileCore_eq_upperCut
#print axioms ThresholdHC.EntropyTailQuantile.quantileCore_residual_work
#print axioms ThresholdHC.EntropyTailQuantile.quantileCore_support
#print axioms ThresholdHC.EntropyTailQuantile.quantileTail
#print axioms ThresholdHC.EntropyTailQuantile.quantileTail_add_core
#print axioms ThresholdHC.EntropyTailQuantile.quantileTail_le
#print axioms ThresholdHC.EntropyTailQuantile.quantileTail_le_selectionCost
#print axioms ThresholdHC.EntropyTailQuantile.quantileTail_le_selectionValue
#print axioms ThresholdHC.EntropyTailQuantile.quantileTail_mass
#print axioms ThresholdHC.EntropyTailQuantile.quantileTail_real_mass
#print axioms ThresholdHC.EntropyTailQuantile.quantileTail_support
#print axioms ThresholdHC.EntropyTailQuantile.quantileTail_threshold_lower
#print axioms ThresholdHC.EntropyTailQuantile.quantileThreshold
#print axioms ThresholdHC.EntropyTailQuantile.quantileThreshold_eq_levelThreshold
#print axioms ThresholdHC.EntropyTailQuantile.quantileThreshold_mass_below
#print axioms ThresholdHC.EntropyTailQuantile.quantileThreshold_properties
#print axioms ThresholdHC.EntropyTailQuantile.quantile_comparison
#print axioms ThresholdHC.EntropyTailQuantile.quantile_comparison_algebra
#print axioms ThresholdHC.EntropyTailQuantile.quantile_comparison_factor_lt_four
#print axioms ThresholdHC.EntropyTailQuantile.quantile_comparison_pointwise
#print axioms ThresholdHC.EntropyTailQuantile.quantile_root_bound
#print axioms ThresholdHC.EntropyTailQuantile.quantile_saturation
#print axioms ThresholdHC.EntropyTailQuantile.quantile_split
#print axioms ThresholdHC.EntropyTailQuantile.scaleSeparated_entropy
#print axioms ThresholdHC.EntropyTailQuantile.selectionCost
#print axioms ThresholdHC.EntropyTailQuantile.selectionValue
#print axioms ThresholdHC.EntropyTailQuantile.selectionValue_le_closedQuantileValue
#print axioms ThresholdHC.EntropyTailQuantile.stieltjes_threshold_properties
#print axioms ThresholdHC.EntropyTailQuantile.sub_quantileCore
#print axioms ThresholdHC.EntropyTailQuantile.tailKernel_integrable
#print axioms ThresholdHC.EntropyTailQuantile.tailKernel_nonneg
#print axioms ThresholdHC.EntropyTailQuantile.tailModulus
#print axioms ThresholdHC.EntropyTailQuantile.tailModulus_add
#print axioms ThresholdHC.EntropyTailQuantile.tailModulus_eq_inverseCost
#print axioms ThresholdHC.EntropyTailQuantile.tailModulus_eq_mass
#print axioms ThresholdHC.EntropyTailQuantile.tailModulus_le_mass
#print axioms ThresholdHC.EntropyTailQuantile.tailModulus_le_sqrt_entropy
#print axioms ThresholdHC.EntropyTailQuantile.tailModulus_mono
#print axioms ThresholdHC.EntropyTailQuantile.tailModulus_nonneg
#print axioms ThresholdHC.EntropyTailQuantile.upperCut
#print axioms ThresholdHC.EntropyTailQuantile.upperCut_add
#print axioms ThresholdHC.EntropyTailQuantile.upperCut_le
#print axioms ThresholdHC.EntropyTailQuantile.upperCut_mono
#print axioms ThresholdHC.EntropyTailQuantile.upperCut_support
#print axioms ThresholdHC.EntropyTailSampling.countedCost_mean
#print axioms ThresholdHC.EntropyTailSampling.countedSum
#print axioms ThresholdHC.EntropyTailSampling.countedSum_integrable
#print axioms ThresholdHC.EntropyTailSampling.countedSum_mean
#print axioms ThresholdHC.EntropyTailSampling.countedSum_memLp
#print axioms ThresholdHC.EntropyTailSampling.countedSum_second
#print axioms ThresholdHC.EntropyTailSampling.countedSum_sq_integrable
#print axioms ThresholdHC.EntropyTailSampling.countedSum_variance
#print axioms ThresholdHC.EntropyTailSampling.empty_prefix_preimage
#print axioms ThresholdHC.EntropyTailSampling.markedPoissonLaw
#print axioms ThresholdHC.EntropyTailSampling.markedPoissonLaw_probability
#print axioms ThresholdHC.EntropyTailSampling.measurable_countedSum
#print axioms ThresholdHC.EntropyTailSampling.measurable_multilevelCost
#print axioms ThresholdHC.EntropyTailSampling.measurable_multilevelValue
#print axioms ThresholdHC.EntropyTailSampling.measurable_poissonAverage
#print axioms ThresholdHC.EntropyTailSampling.measurable_prefixSum
#print axioms ThresholdHC.EntropyTailSampling.measurable_raceMean
#print axioms ThresholdHC.EntropyTailSampling.multilevelCost
#print axioms ThresholdHC.EntropyTailSampling.multilevelCost_integrable
#print axioms ThresholdHC.EntropyTailSampling.multilevelCost_mean
#print axioms ThresholdHC.EntropyTailSampling.multilevelLaw
#print axioms ThresholdHC.EntropyTailSampling.multilevelLaw_probability
#print axioms ThresholdHC.EntropyTailSampling.multilevelValue
#print axioms ThresholdHC.EntropyTailSampling.multilevelValue_mean
#print axioms ThresholdHC.EntropyTailSampling.multilevelValue_memLp
#print axioms ThresholdHC.EntropyTailSampling.multilevelValue_mse
#print axioms ThresholdHC.EntropyTailSampling.multilevelValue_variance
#print axioms ThresholdHC.EntropyTailSampling.negativeBankTest_zero
#print axioms ThresholdHC.EntropyTailSampling.poissonAverage
#print axioms ThresholdHC.EntropyTailSampling.poissonAverage_mean
#print axioms ThresholdHC.EntropyTailSampling.poissonAverage_memLp
#print axioms ThresholdHC.EntropyTailSampling.poissonAverage_mse
#print axioms ThresholdHC.EntropyTailSampling.poissonAverage_squaredRisk
#print axioms ThresholdHC.EntropyTailSampling.poissonAverage_variance
#print axioms ThresholdHC.EntropyTailSampling.positiveBankTest_zero
#print axioms ThresholdHC.EntropyTailSampling.prefixSum
#print axioms ThresholdHC.EntropyTailSampling.prefixSum_mean
#print axioms ThresholdHC.EntropyTailSampling.prefixSum_memLp
#print axioms ThresholdHC.EntropyTailSampling.prefixSum_norm_le
#print axioms ThresholdHC.EntropyTailSampling.prefixSum_second
#print axioms ThresholdHC.EntropyTailSampling.prefix_projection_preserving
#print axioms ThresholdHC.EntropyTailSampling.probability_weight_le_one
#print axioms ThresholdHC.EntropyTailSampling.raceCost_pos_of_no_empty_crossing
#print axioms ThresholdHC.EntropyTailSampling.raceMean
#print axioms ThresholdHC.EntropyTailSampling.raceMean_bias
#print axioms ThresholdHC.EntropyTailSampling.raceMean_bounds
#print axioms ThresholdHC.EntropyTailSampling.raceValue_bias_le
#print axioms ThresholdHC.EntropyTailSampling.raceValue_bounds
#print axioms ThresholdHC.EntropyTailSampling.race_difference_coin_moment
#print axioms ThresholdHC.EntropyTailSampling.race_difference_population_moment
#print axioms ThresholdHC.EntropyTailSampling.race_difference_sq_integrable
#print axioms ThresholdHC.EntropyTailSampling.race_error_integral
#print axioms ThresholdHC.EntropyTailSampling.race_population_work
#print axioms ThresholdHC.EntropyTailSampling.scheduled_raceCost_pos
#print axioms ThresholdHC.EntropyTailUpper.PrefixTest
#print axioms ThresholdHC.EntropyTailUpper.allNegativeLaw
#print axioms ThresholdHC.EntropyTailUpper.allNegativeSignLaw
#print axioms ThresholdHC.EntropyTailUpper.allocationCertificate
#print axioms ThresholdHC.EntropyTailUpper.allocationCertificate_pos
#print axioms ThresholdHC.EntropyTailUpper.allocationMean
#print axioms ThresholdHC.EntropyTailUpper.allocationMean_pos
#print axioms ThresholdHC.EntropyTailUpper.allocationMean_variance
#print axioms ThresholdHC.EntropyTailUpper.allocationMean_work
#print axioms ThresholdHC.EntropyTailUpper.allocation_certificate_optimal
#print axioms ThresholdHC.EntropyTailUpper.bandEdge_le_half
#print axioms ThresholdHC.EntropyTailUpper.bankRace
#print axioms ThresholdHC.EntropyTailUpper.bank_population_error_le
#print axioms ThresholdHC.EntropyTailUpper.bank_raceRounds_le_score
#print axioms ThresholdHC.EntropyTailUpper.bank_race_negative_work
#print axioms ThresholdHC.EntropyTailUpper.bank_race_positive_work
#print axioms ThresholdHC.EntropyTailUpper.bitScoreMean
#print axioms ThresholdHC.EntropyTailUpper.boundedFirst
#print axioms ThresholdHC.EntropyTailUpper.boundedFirst_before
#print axioms ThresholdHC.EntropyTailUpper.boundedFirst_congr_until
#print axioms ThresholdHC.EntropyTailUpper.boundedFirst_le_of_hit
#print axioms ThresholdHC.EntropyTailUpper.boundedFirst_spec
#print axioms ThresholdHC.EntropyTailUpper.bounded_count_tail_sum
#print axioms ThresholdHC.EntropyTailUpper.bounded_wald
#print axioms ThresholdHC.EntropyTailUpper.classifierStop_by_prefix
#print axioms ThresholdHC.EntropyTailUpper.everPrefixHit
#print axioms ThresholdHC.EntropyTailUpper.everPrefixHit_eq_iUnion
#print axioms ThresholdHC.EntropyTailUpper.ever_negativeBankTest
#print axioms ThresholdHC.EntropyTailUpper.ever_positiveBankTest
#print axioms ThresholdHC.EntropyTailUpper.finite_geometric_sum_le
#print axioms ThresholdHC.EntropyTailUpper.firstPrefixHit
#print axioms ThresholdHC.EntropyTailUpper.firstPrefixHit_disjoint
#print axioms ThresholdHC.EntropyTailUpper.firstPrefixHit_eq_preimage
#print axioms ThresholdHC.EntropyTailUpper.firstPrefixHit_ext
#print axioms ThresholdHC.EntropyTailUpper.gaussian_relative_bounds
#print axioms ThresholdHC.EntropyTailUpper.geometric_work_bound
#print axioms ThresholdHC.EntropyTailUpper.integrable_nullLaplace
#print axioms ThresholdHC.EntropyTailUpper.integrable_ordinaryErrorKernel
#print axioms ThresholdHC.EntropyTailUpper.integrable_raceCost
#print axioms ThresholdHC.EntropyTailUpper.integrable_racePopulationError
#print axioms ThresholdHC.EntropyTailUpper.integrable_scoreStop
#print axioms ThresholdHC.EntropyTailUpper.integrable_stopped_score
#print axioms ThresholdHC.EntropyTailUpper.integrable_survives
#print axioms ThresholdHC.EntropyTailUpper.integrable_survives_score
#print axioms ThresholdHC.EntropyTailUpper.integrable_tapeEventProbability
#print axioms ThresholdHC.EntropyTailUpper.integral_bitScore
#print axioms ThresholdHC.EntropyTailUpper.integral_survives
#print axioms ThresholdHC.EntropyTailUpper.integral_survives_score
#print axioms ThresholdHC.EntropyTailUpper.inv_one_sub_exp_neg_le
#print axioms ThresholdHC.EntropyTailUpper.logPlus
#print axioms ThresholdHC.EntropyTailUpper.logPlus_eq_log_max
#print axioms ThresholdHC.EntropyTailUpper.logPlus_le_half_sq
#print axioms ThresholdHC.EntropyTailUpper.logPlus_le_self
#print axioms ThresholdHC.EntropyTailUpper.logPlus_nonneg
#print axioms ThresholdHC.EntropyTailUpper.logPlus_three_term
#print axioms ThresholdHC.EntropyTailUpper.log_surcharge_bound
#print axioms ThresholdHC.EntropyTailUpper.measurableSet_everPrefixHit
#print axioms ThresholdHC.EntropyTailUpper.measurableSet_firstPrefixHit
#print axioms ThresholdHC.EntropyTailUpper.measurable_parityTape
#print axioms ThresholdHC.EntropyTailUpper.measurable_prefixSearchCost
#print axioms ThresholdHC.EntropyTailUpper.measurable_prefixSearchValue
#print axioms ThresholdHC.EntropyTailUpper.measurable_raceConditionalError
#print axioms ThresholdHC.EntropyTailUpper.measurable_raceCost
#print axioms ThresholdHC.EntropyTailUpper.measurable_raceRounds
#print axioms ThresholdHC.EntropyTailUpper.measurable_raceValue
#print axioms ThresholdHC.EntropyTailUpper.measurable_survives
#print axioms ThresholdHC.EntropyTailUpper.measurable_tapeEventProbability
#print axioms ThresholdHC.EntropyTailUpper.measure_everPrefixHit_le
#print axioms ThresholdHC.EntropyTailUpper.measure_firstPrefixHit_le
#print axioms ThresholdHC.EntropyTailUpper.negativeBankEvent
#print axioms ThresholdHC.EntropyTailUpper.negativeBankTest
#print axioms ThresholdHC.EntropyTailUpper.negativeBitScore
#print axioms ThresholdHC.EntropyTailUpper.negativeBitScore_affine
#print axioms ThresholdHC.EntropyTailUpper.negativeBitScore_le_one
#print axioms ThresholdHC.EntropyTailUpper.negativeBitScore_mean
#print axioms ThresholdHC.EntropyTailUpper.negativeReferenceDrift
#print axioms ThresholdHC.EntropyTailUpper.negativeReferenceDrift_eq
#print axioms ThresholdHC.EntropyTailUpper.negativeReferenceDrift_lower
#print axioms ThresholdHC.EntropyTailUpper.negative_bank_error
#print axioms ThresholdHC.EntropyTailUpper.negative_bank_probability
#print axioms ThresholdHC.EntropyTailUpper.negative_prefix_gaussian
#print axioms ThresholdHC.EntropyTailUpper.negative_prefix_gaussian_interior
#print axioms ThresholdHC.EntropyTailUpper.negative_prefix_score
#print axioms ThresholdHC.EntropyTailUpper.negative_reference_crossing_dominates
#print axioms ThresholdHC.EntropyTailUpper.negative_reference_error
#print axioms ThresholdHC.EntropyTailUpper.negative_scoreStop_work
#print axioms ThresholdHC.EntropyTailUpper.negative_score_crossing
#print axioms ThresholdHC.EntropyTailUpper.negative_score_likelihood
#print axioms ThresholdHC.EntropyTailUpper.nullLaplace
#print axioms ThresholdHC.EntropyTailUpper.nullLaplace_le_mass
#print axioms ThresholdHC.EntropyTailUpper.nullLaplace_three_piece
#print axioms ThresholdHC.EntropyTailUpper.null_event_mixture
#print axioms ThresholdHC.EntropyTailUpper.null_prefix_gaussian
#print axioms ThresholdHC.EntropyTailUpper.null_prefix_gaussian_ennreal
#print axioms ThresholdHC.EntropyTailUpper.null_prefix_real
#print axioms ThresholdHC.EntropyTailUpper.ordinaryErrorKernel
#print axioms ThresholdHC.EntropyTailUpper.ordinaryWorkKernel
#print axioms ThresholdHC.EntropyTailUpper.ordinary_conditional_error
#print axioms ThresholdHC.EntropyTailUpper.ordinary_conditional_work
#print axioms ThresholdHC.EntropyTailUpper.parityTape
#print axioms ThresholdHC.EntropyTailUpper.parityTape_event
#print axioms ThresholdHC.EntropyTailUpper.parityTape_integral
#print axioms ThresholdHC.EntropyTailUpper.parityTape_measurePreserving
#print axioms ThresholdHC.EntropyTailUpper.parityTape_prefix_ext
#print axioms ThresholdHC.EntropyTailUpper.poissonWeight
#print axioms ThresholdHC.EntropyTailUpper.poissonWeight_factorial_hasSum
#print axioms ThresholdHC.EntropyTailUpper.poissonWeight_first_hasSum
#print axioms ThresholdHC.EntropyTailUpper.poissonWeight_second_hasSum
#print axioms ThresholdHC.EntropyTailUpper.poissonWeight_succ
#print axioms ThresholdHC.EntropyTailUpper.poisson_count_integrable
#print axioms ThresholdHC.EntropyTailUpper.poisson_count_mean
#print axioms ThresholdHC.EntropyTailUpper.poisson_count_second_moment
#print axioms ThresholdHC.EntropyTailUpper.poisson_count_sq_integrable
#print axioms ThresholdHC.EntropyTailUpper.positiveAllowance
#print axioms ThresholdHC.EntropyTailUpper.positiveAllowance_covers
#print axioms ThresholdHC.EntropyTailUpper.positiveAllowance_ge_one
#print axioms ThresholdHC.EntropyTailUpper.positiveBankEvent
#print axioms ThresholdHC.EntropyTailUpper.positiveBankLaw
#print axioms ThresholdHC.EntropyTailUpper.positiveBankLaw_lower
#print axioms ThresholdHC.EntropyTailUpper.positiveBankLaw_probability
#print axioms ThresholdHC.EntropyTailUpper.positiveBankTest
#print axioms ThresholdHC.EntropyTailUpper.positiveBitScore
#print axioms ThresholdHC.EntropyTailUpper.positiveBitScore_affine
#print axioms ThresholdHC.EntropyTailUpper.positiveReference
#print axioms ThresholdHC.EntropyTailUpper.positiveReferenceDrift_lower
#print axioms ThresholdHC.EntropyTailUpper.positive_bank_error
#print axioms ThresholdHC.EntropyTailUpper.positive_bank_integrated_probability
#print axioms ThresholdHC.EntropyTailUpper.positive_bank_of_score
#print axioms ThresholdHC.EntropyTailUpper.positive_prefix_score
#print axioms ThresholdHC.EntropyTailUpper.positive_prefix_score_lower
#print axioms ThresholdHC.EntropyTailUpper.positive_raceRounds_work
#print axioms ThresholdHC.EntropyTailUpper.positive_race_survival
#print axioms ThresholdHC.EntropyTailUpper.positive_score_likelihood
#print axioms ThresholdHC.EntropyTailUpper.prefixSearchCost
#print axioms ThresholdHC.EntropyTailUpper.prefixSearchCost_ext
#print axioms ThresholdHC.EntropyTailUpper.prefixSearchCost_le
#print axioms ThresholdHC.EntropyTailUpper.prefixSearchProcedure
#print axioms ThresholdHC.EntropyTailUpper.prefixSearchValue
#print axioms ThresholdHC.EntropyTailUpper.prefixSearchValue_ext
#print axioms ThresholdHC.EntropyTailUpper.prefix_count_eq
#print axioms ThresholdHC.EntropyTailUpper.prefix_indep_next
#print axioms ThresholdHC.EntropyTailUpper.raceConditionalError
#print axioms ThresholdHC.EntropyTailUpper.raceCost
#print axioms ThresholdHC.EntropyTailUpper.raceCost_le
#print axioms ThresholdHC.EntropyTailUpper.raceHit
#print axioms ThresholdHC.EntropyTailUpper.raceHit_prefix_ext
#print axioms ThresholdHC.EntropyTailUpper.racePopulationError
#print axioms ThresholdHC.EntropyTailUpper.raceProcedure
#print axioms ThresholdHC.EntropyTailUpper.raceRounds
#print axioms ThresholdHC.EntropyTailUpper.raceRounds_hit
#print axioms ThresholdHC.EntropyTailUpper.raceRounds_le
#print axioms ThresholdHC.EntropyTailUpper.raceRounds_le_bank
#print axioms ThresholdHC.EntropyTailUpper.raceRounds_le_ordinary
#print axioms ThresholdHC.EntropyTailUpper.raceRounds_prefix_ext
#print axioms ThresholdHC.EntropyTailUpper.raceValue
#print axioms ThresholdHC.EntropyTailUpper.raceValue_zero_or_one
#print axioms ThresholdHC.EntropyTailUpper.race_error_negative_bound
#print axioms ThresholdHC.EntropyTailUpper.race_error_negative_subset
#print axioms ThresholdHC.EntropyTailUpper.race_error_positive_bound
#print axioms ThresholdHC.EntropyTailUpper.race_error_positive_subset
#print axioms ThresholdHC.EntropyTailUpper.race_expected_work_le_ordinary
#print axioms ThresholdHC.EntropyTailUpper.race_prefix_ext
#print axioms ThresholdHC.EntropyTailUpper.reference_log_base
#print axioms ThresholdHC.EntropyTailUpper.reference_log_overshoot
#print axioms ThresholdHC.EntropyTailUpper.reference_log_ratio
#print axioms ThresholdHC.EntropyTailUpper.scoreStop
#print axioms ThresholdHC.EntropyTailUpper.scoreStop_expected_mul_drift_le
#print axioms ThresholdHC.EntropyTailUpper.scoreStop_overshoot
#print axioms ThresholdHC.EntropyTailUpper.scoreTest
#print axioms ThresholdHC.EntropyTailUpper.scoreTest_prefix
#print axioms ThresholdHC.EntropyTailUpper.stopped_by_prefix
#print axioms ThresholdHC.EntropyTailUpper.stopped_count_eq
#print axioms ThresholdHC.EntropyTailUpper.stopped_sum_eq
#print axioms ThresholdHC.EntropyTailUpper.streamProb_nonneg_of_unit
#print axioms ThresholdHC.EntropyTailUpper.survives
#print axioms ThresholdHC.EntropyTailUpper.survives_prefix
#print axioms ThresholdHC.EntropyTailUpper.tapeEventProbability
#print axioms ThresholdHC.EntropyTailUpper.tape_prefix_lower_tail
#print axioms ThresholdHC.EntropyTailUpper.tape_prefix_mass
#print axioms ThresholdHC.EntropyTailUpper.tape_prefix_subgaussian
#print axioms ThresholdHC.EntropyTailUpper.tape_prefix_upper_tail
#print axioms ThresholdHC.EntropyTailUpper.threePieceEnvelope
#print axioms ThresholdHC.EntropyTailUpper.threePieceEnvelope_nonneg
#print axioms ThresholdHC.EntropyTailUpper.tiltNormalizer
#print axioms ThresholdHC.EntropyTailUpper.tiltNormalizer_bounds
#print axioms ThresholdHC.EntropyTailUpper.tiltedParameter
#print axioms ThresholdHC.EntropyTailUpper.tilted_bit_bound
#print axioms ThresholdHC.EntropyTailUpper.tilted_prefix_bound
#print axioms ThresholdHC.Genie.AllCountIndex
#print axioms ThresholdHC.Genie.AllFourCoordinates
#print axioms ThresholdHC.Genie.AtomBox
#print axioms ThresholdHC.Genie.AtomConicFeasible
#print axioms ThresholdHC.Genie.AtomConicPoint
#print axioms ThresholdHC.Genie.BellmanEnvelope
#print axioms ThresholdHC.Genie.FiniteGenieCones
#print axioms ThresholdHC.Genie.LatentCones
#print axioms ThresholdHC.Genie.LatentState
#print axioms ThresholdHC.Genie.LatentTapeState
#print axioms ThresholdHC.Genie.PriorDomain
#print axioms ThresholdHC.Genie.absorbedPriors_infiniteDualRatio
#print axioms ThresholdHC.Genie.absorbedPriors_infiniteInformation_le
#print axioms ThresholdHC.Genie.allFourPriorCoordinates
#print axioms ThresholdHC.Genie.allFourPriorMomentImage
#print axioms ThresholdHC.Genie.allFourPriorMomentImage_compact
#print axioms ThresholdHC.Genie.allFourPriorMomentImage_iff
#print axioms ThresholdHC.Genie.allPriorCoordinates
#print axioms ThresholdHC.Genie.allPriorMomentImage
#print axioms ThresholdHC.Genie.allPriorMomentImage_compact_convex
#print axioms ThresholdHC.Genie.allPriorMomentImage_nonempty
#print axioms ThresholdHC.Genie.arrayAt_bellmanEnvelopeArray
#print axioms ThresholdHC.Genie.arrayAt_extendArray
#print axioms ThresholdHC.Genie.arrayAt_nonneg
#print axioms ThresholdHC.Genie.arrayAt_truncate_continue
#print axioms ThresholdHC.Genie.arrayAt_truncate_stop
#print axioms ThresholdHC.Genie.atomBox_of_prior
#print axioms ThresholdHC.Genie.atomConicFeasible_of_priors
#print axioms ThresholdHC.Genie.atomConicObjective
#print axioms ThresholdHC.Genie.atomConicObjective_of_priors
#print axioms ThresholdHC.Genie.atomConicValue
#print axioms ThresholdHC.Genie.atomConicValue_eq_genieSquared
#print axioms ThresholdHC.Genie.atomConicVariableCount
#print axioms ThresholdHC.Genie.atomConicVariableCount_bound
#print axioms ThresholdHC.Genie.atomConic_realization
#print axioms ThresholdHC.Genie.atomPointOfPriors
#print axioms ThresholdHC.Genie.atomPrefixCoefficient
#print axioms ThresholdHC.Genie.atomSignLaw
#print axioms ThresholdHC.Genie.atomSignLaw_apply
#print axioms ThresholdHC.Genie.atomSignLaw_rare
#print axioms ThresholdHC.Genie.bellmanEnvelopeArray
#print axioms ThresholdHC.Genie.bellman_le_envelope
#print axioms ThresholdHC.Genie.bellman_scale
#print axioms ThresholdHC.Genie.binary_difference_sq_bound
#print axioms ThresholdHC.Genie.bitValue
#print axioms ThresholdHC.Genie.capped_reward_le_truncated_reveal
#print axioms ThresholdHC.Genie.compact_decreasing_maximum
#print axioms ThresholdHC.Genie.continue_arrayAt_ge_cap
#print axioms ThresholdHC.Genie.countMean_extendArray
#print axioms ThresholdHC.Genie.countState_card_le_square
#print axioms ThresholdHC.Genie.directRiskProfile
#print axioms ThresholdHC.Genie.directRiskProfile_greatest
#print axioms ThresholdHC.Genie.directRiskProfile_max
#print axioms ThresholdHC.Genie.directRiskProfile_square
#print axioms ThresholdHC.Genie.directRiskScale
#print axioms ThresholdHC.Genie.directRiskScale_mem
#print axioms ThresholdHC.Genie.directRiskSquared
#print axioms ThresholdHC.Genie.direct_large_scale
#print axioms ThresholdHC.Genie.direct_large_scale_data
#print axioms ThresholdHC.Genie.direct_pair_risk
#print axioms ThresholdHC.Genie.direct_small_scale
#print axioms ThresholdHC.Genie.domainPriors
#print axioms ThresholdHC.Genie.domainPriors_admissible
#print axioms ThresholdHC.Genie.domainPriors_coordinates
#print axioms ThresholdHC.Genie.domain_dualRatio_upperSemicontinuous
#print axioms ThresholdHC.Genie.dualRatio_antitone
#print axioms ThresholdHC.Genie.dualRatio_coordinates_congr
#print axioms ThresholdHC.Genie.dualRatio_upperSemicontinuous
#print axioms ThresholdHC.Genie.dualValue_eq_domain_sup
#print axioms ThresholdHC.Genie.eRawChildren
#print axioms ThresholdHC.Genie.eRawLayer
#print axioms ThresholdHC.Genie.eRawLayer_mono
#print axioms ThresholdHC.Genie.eRaw_fullCap_layer
#print axioms ThresholdHC.Genie.eRaw_fullCap_reward
#print axioms ThresholdHC.Genie.eRaw_harmonic_conservation
#print axioms ThresholdHC.Genie.eRaw_layer_conservation
#print axioms ThresholdHC.Genie.eRaw_recursion
#print axioms ThresholdHC.Genie.eRaw_root_total
#print axioms ThresholdHC.Genie.eRaw_tail_harmonic
#print axioms ThresholdHC.Genie.eRaw_terminal
#print axioms ThresholdHC.Genie.eRaw_truncate_stop_before
#print axioms ThresholdHC.Genie.eRaw_truncate_stop_terminal
#print axioms ThresholdHC.Genie.empiricalMean
#print axioms ThresholdHC.Genie.envelope_root
#print axioms ThresholdHC.Genie.exists_bellmanEnvelope_iff
#print axioms ThresholdHC.Genie.exists_scaled_atom_prior
#print axioms ThresholdHC.Genie.extendArray
#print axioms ThresholdHC.Genie.extendCertificate
#print axioms ThresholdHC.Genie.extendFlow
#print axioms ThresholdHC.Genie.extendFlow_cone
#print axioms ThresholdHC.Genie.extendFlow_intensity
#print axioms ThresholdHC.Genie.feasible_extendCertificate
#print axioms ThresholdHC.Genie.finiteGenieCones_envelope
#print axioms ThresholdHC.Genie.finiteGenieCones_iff_bellman
#print axioms ThresholdHC.Genie.finiteGenieCones_iff_price
#print axioms ThresholdHC.Genie.finiteGenieCones_objective_attained
#print axioms ThresholdHC.Genie.finiteGenieCones_objective_le
#print axioms ThresholdHC.Genie.finiteGenieCones_of_envelope
#print axioms ThresholdHC.Genie.finiteGenieCones_zero
#print axioms ThresholdHC.Genie.finiteGenieConicValue
#print axioms ThresholdHC.Genie.finiteGenieConicValue_eq
#print axioms ThresholdHC.Genie.finiteRevealBound
#print axioms ThresholdHC.Genie.finiteRevealBound_exact
#print axioms ThresholdHC.Genie.finiteRevealBound_lower
#print axioms ThresholdHC.Genie.finite_latentDivergence
#print axioms ThresholdHC.Genie.finite_latent_perspectives
#print axioms ThresholdHC.Genie.finite_latent_perspectives_ae
#print axioms ThresholdHC.Genie.finite_law_lintegral
#print axioms ThresholdHC.Genie.finite_posterior_secondMoment
#print axioms ThresholdHC.Genie.finite_prefixCoefficient
#print axioms ThresholdHC.Genie.finite_prior_mean
#print axioms ThresholdHC.Genie.finite_revealReward
#print axioms ThresholdHC.Genie.finite_revealReward_toReal
#print axioms ThresholdHC.Genie.finite_scaled_mean
#print axioms ThresholdHC.Genie.finite_scaled_prefixCoefficient
#print axioms ThresholdHC.Genie.flowInformation_extendFlow
#print axioms ThresholdHC.Genie.flowInformation_le_genie
#print axioms ThresholdHC.Genie.flowInformation_le_truncated_reveal
#print axioms ThresholdHC.Genie.flow_ratio_lowerSemicontinuous
#print axioms ThresholdHC.Genie.flow_ratio_perspective_sum
#print axioms ThresholdHC.Genie.genieBellmanRatio
#print axioms ThresholdHC.Genie.genieBellmanRatio_nonneg
#print axioms ThresholdHC.Genie.genieDualRatio
#print axioms ThresholdHC.Genie.genieDualRatio_le_infinite
#print axioms ThresholdHC.Genie.genieDualRatio_real
#print axioms ThresholdHC.Genie.genieDualRatio_tendsto
#print axioms ThresholdHC.Genie.genieFlowInformation
#print axioms ThresholdHC.Genie.genieFlowInformation_finite
#print axioms ThresholdHC.Genie.genieFlowInformation_fullCap
#print axioms ThresholdHC.Genie.genieFlowInformation_gap
#print axioms ThresholdHC.Genie.genieFlowInformation_le_add_residual
#print axioms ThresholdHC.Genie.genieFlowInformation_le_latent
#print axioms ThresholdHC.Genie.genieFlowInformation_le_truncated
#print axioms ThresholdHC.Genie.genieFlowInformation_toReal_raw
#print axioms ThresholdHC.Genie.genieFlowInformation_truncate
#print axioms ThresholdHC.Genie.genieFlowScore_information
#print axioms ThresholdHC.Genie.genieInformationRatio
#print axioms ThresholdHC.Genie.genieInformationRatio_antitone
#print axioms ThresholdHC.Genie.genieInformationRatio_antitone_cap
#print axioms ThresholdHC.Genie.genieInformationRatio_bellman_attained
#print axioms ThresholdHC.Genie.genieInformationRatio_bellman_certificate
#print axioms ThresholdHC.Genie.genieInformationRatio_bellman_zero
#print axioms ThresholdHC.Genie.genieInformationRatio_le_add_residual
#print axioms ThresholdHC.Genie.genieInformationRatio_le_genieBellmanRatio
#print axioms ThresholdHC.Genie.genieInformationRatio_le_latent
#print axioms ThresholdHC.Genie.genieInformationRatio_tendsto
#print axioms ThresholdHC.Genie.genieInformationRatio_top_iff
#print axioms ThresholdHC.Genie.geniePrefixInformation
#print axioms ThresholdHC.Genie.geniePrefixInformation_finite
#print axioms ThresholdHC.Genie.geniePrefixInformation_le_reveal
#print axioms ThresholdHC.Genie.genieReward
#print axioms ThresholdHC.Genie.genieSquared
#print axioms ThresholdHC.Genie.genieSquared_le_infinite
#print axioms ThresholdHC.Genie.genieSquared_mono
#print axioms ThresholdHC.Genie.genieSquared_sup_eq_infinite
#print axioms ThresholdHC.Genie.genieSquared_tendsto
#print axioms ThresholdHC.Genie.genieValue
#print axioms ThresholdHC.Genie.genieValue_le_infinite
#print axioms ThresholdHC.Genie.genieValue_mono
#print axioms ThresholdHC.Genie.genieValue_positive
#print axioms ThresholdHC.Genie.genieValue_tendsto
#print axioms ThresholdHC.Genie.genie_bellman_direct_squared_risk
#print axioms ThresholdHC.Genie.genie_direct_risk
#print axioms ThresholdHC.Genie.genie_direct_squared_risk
#print axioms ThresholdHC.Genie.genie_information_error
#print axioms ThresholdHC.Genie.genie_risk_bracket
#print axioms ThresholdHC.Genie.genie_stopping_certificate
#print axioms ThresholdHC.Genie.genie_stopping_eventually
#print axioms ThresholdHC.Genie.genie_stopping_terminates
#print axioms ThresholdHC.Genie.infiniteDualRatio
#print axioms ThresholdHC.Genie.infiniteDualRatio_eq_iInf
#print axioms ThresholdHC.Genie.infiniteDualRatio_le_genieSup
#print axioms ThresholdHC.Genie.infiniteDualRatio_le_genieSup_of_finite
#print axioms ThresholdHC.Genie.infiniteDualValue
#print axioms ThresholdHC.Genie.infiniteInformationRatio
#print axioms ThresholdHC.Genie.infiniteInformationRatio_le_genie
#print axioms ThresholdHC.Genie.infiniteMidpointSquared
#print axioms ThresholdHC.Genie.infiniteMidpointValue
#print axioms ThresholdHC.Genie.infiniteProgramValue
#print axioms ThresholdHC.Genie.infiniteProgramValue_le_cap
#print axioms ThresholdHC.Genie.infiniteProgramValue_ne_top
#print axioms ThresholdHC.Genie.infiniteProgramValue_sq
#print axioms ThresholdHC.Genie.infinite_divergence_counterexample
#print axioms ThresholdHC.Genie.infinite_dual_positive_attained
#print axioms ThresholdHC.Genie.infinite_four_prior_duality
#print axioms ThresholdHC.Genie.infinite_midpoint_comparison
#print axioms ThresholdHC.Genie.infinite_midpoint_squared_comparison
#print axioms ThresholdHC.Genie.infinite_program_comparison
#print axioms ThresholdHC.Genie.infinite_program_positive
#print axioms ThresholdHC.Genie.infinite_weak_duality
#print axioms ThresholdHC.Genie.informationRatio_le_earlier_genie
#print axioms ThresholdHC.Genie.informationRatio_le_genie
#print axioms ThresholdHC.Genie.informationRatio_le_infinite
#print axioms ThresholdHC.Genie.informationRatio_lowerSemicontinuous
#print axioms ThresholdHC.Genie.informationRatio_mono
#print axioms ThresholdHC.Genie.informationRatio_tendsto
#print axioms ThresholdHC.Genie.latentCones_bounds
#print axioms ThresholdHC.Genie.latentCones_finite
#print axioms ThresholdHC.Genie.latentCones_of_finite
#print axioms ThresholdHC.Genie.latentDivergence
#print axioms ThresholdHC.Genie.latentObservedTape
#print axioms ThresholdHC.Genie.latentParameter
#print axioms ThresholdHC.Genie.latentParameter_embedding
#print axioms ThresholdHC.Genie.latentParameter_injective
#print axioms ThresholdHC.Genie.latentReference
#print axioms ThresholdHC.Genie.latentReference_integral
#print axioms ThresholdHC.Genie.latentReference_lintegral
#print axioms ThresholdHC.Genie.latentReference_probability
#print axioms ThresholdHC.Genie.latentScore
#print axioms ThresholdHC.Genie.latentScore_integrable
#print axioms ThresholdHC.Genie.latentScore_memLp_two
#print axioms ThresholdHC.Genie.latentScore_secondMoment
#print axioms ThresholdHC.Genie.latentSelector
#print axioms ThresholdHC.Genie.latentTapeLaw
#print axioms ThresholdHC.Genie.latentTapeLaw_probability
#print axioms ThresholdHC.Genie.latentTapeScore
#print axioms ThresholdHC.Genie.latentTapeScore_integrable
#print axioms ThresholdHC.Genie.latentTapeScore_secondMoment
#print axioms ThresholdHC.Genie.latentTape_parameter_ae
#print axioms ThresholdHC.Genie.latentTape_score_reconstruction
#print axioms ThresholdHC.Genie.latent_prefix_integral
#print axioms ThresholdHC.Genie.latent_prefix_mass
#print axioms ThresholdHC.Genie.latent_prefix_score
#print axioms ThresholdHC.Genie.latent_score_posterior_tendsto
#print axioms ThresholdHC.Genie.lowerSemicontinuous_perspective
#print axioms ThresholdHC.Genie.measurable_bitValue
#print axioms ThresholdHC.Genie.measurable_empiricalMean
#print axioms ThresholdHC.Genie.measurable_latentObservedTape
#print axioms ThresholdHC.Genie.measurable_latentParameter
#print axioms ThresholdHC.Genie.measurable_latentScore
#print axioms ThresholdHC.Genie.measurable_latentSelector
#print axioms ThresholdHC.Genie.measurable_latentTapeScore
#print axioms ThresholdHC.Genie.measurable_parameterScore
#print axioms ThresholdHC.Genie.measurable_perspective
#print axioms ThresholdHC.Genie.measurable_prefixLikelihood
#print axioms ThresholdHC.Genie.measurable_revealIntegrand
#print axioms ThresholdHC.Genie.measurable_tapeParameter
#print axioms ThresholdHC.Genie.observationFiltration
#print axioms ThresholdHC.Genie.observationFiltration_eq_comap
#print axioms ThresholdHC.Genie.observedPrefix
#print axioms ThresholdHC.Genie.observedPrefix_measurable
#print axioms ThresholdHC.Genie.observedTape_measurable_iSup
#print axioms ThresholdHC.Genie.ofReal_integral_le_lintegral_positive
#print axioms ThresholdHC.Genie.parameterScore
#print axioms ThresholdHC.Genie.parameterScore_latent
#print axioms ThresholdHC.Genie.parameter_mixture_identification
#print axioms ThresholdHC.Genie.perspective_eq_iSup_test
#print axioms ThresholdHC.Genie.perspective_integral_le
#print axioms ThresholdHC.Genie.perspective_le_finite_iff
#print axioms ThresholdHC.Genie.perspective_neg_left
#print axioms ThresholdHC.Genie.perspective_scale_reference
#print axioms ThresholdHC.Genie.posterior_secondMoment_eq_terminal
#print axioms ThresholdHC.Genie.prefixDensity
#print axioms ThresholdHC.Genie.prefixDensity_information_le
#print axioms ThresholdHC.Genie.prefixDensity_integrable
#print axioms ThresholdHC.Genie.prefixDensity_nonneg
#print axioms ThresholdHC.Genie.prefixInformation_le_genie
#print axioms ThresholdHC.Genie.prefixInformation_le_revealReward
#print axioms ThresholdHC.Genie.priorDomainCompact
#print axioms ThresholdHC.Genie.priorDomain_nonempty
#print axioms ThresholdHC.Genie.priorPoint
#print axioms ThresholdHC.Genie.programSquared_antitone
#print axioms ThresholdHC.Genie.programValue_antitone
#print axioms ThresholdHC.Genie.programValue_tendsto
#print axioms ThresholdHC.Genie.quadratic_slack_iff
#print axioms ThresholdHC.Genie.quadratic_test_le_perspective
#print axioms ThresholdHC.Genie.rawArray_nonneg
#print axioms ThresholdHC.Genie.rawLayer_above_cap
#print axioms ThresholdHC.Genie.rawLayer_extendArray
#print axioms ThresholdHC.Genie.raw_stop_le_choose
#print axioms ThresholdHC.Genie.raw_stopping_depth
#print axioms ThresholdHC.Genie.raw_truncate_continue_le
#print axioms ThresholdHC.Genie.raw_truncate_stop
#print axioms ThresholdHC.Genie.regularizedPriors
#print axioms ThresholdHC.Genie.regularizedPriors_admissible
#print axioms ThresholdHC.Genie.regularized_count_reference
#print axioms ThresholdHC.Genie.regularized_flowInformation
#print axioms ThresholdHC.Genie.regularized_infiniteInformation
#print axioms ThresholdHC.Genie.regularized_informationRatio
#print axioms ThresholdHC.Genie.regularized_latentDivergence_bound
#print axioms ThresholdHC.Genie.regularized_latent_perspective
#print axioms ThresholdHC.Genie.revealGap
#print axioms ThresholdHC.Genie.revealResidual
#print axioms ThresholdHC.Genie.revealResidual_add_terminal
#print axioms ThresholdHC.Genie.revealResidual_eq_sub
#print axioms ThresholdHC.Genie.revealResidual_tendsto_zero
#print axioms ThresholdHC.Genie.revealReward
#print axioms ThresholdHC.Genie.revealReward_children
#print axioms ThresholdHC.Genie.revealReward_eq_add_gap
#print axioms ThresholdHC.Genie.revealReward_le_latentDivergence
#print axioms ThresholdHC.Genie.revealReward_root
#print axioms ThresholdHC.Genie.rootBellman_scale
#print axioms ThresholdHC.Genie.scale_objective_attained
#print axioms ThresholdHC.Genie.scale_objective_bound
#print axioms ThresholdHC.Genie.scaled_genie_root
#print axioms ThresholdHC.Genie.singularExamplePriors
#print axioms ThresholdHC.Genie.singularExample_admissible
#print axioms ThresholdHC.Genie.singularExample_genie_top
#print axioms ThresholdHC.Genie.singularExample_latentDivergence
#print axioms ThresholdHC.Genie.singularExample_no_pointwise_convergence
#print axioms ThresholdHC.Genie.singularVariancePrior
#print axioms ThresholdHC.Genie.singularVariancePrior_mean
#print axioms ThresholdHC.Genie.singular_flow_information
#print axioms ThresholdHC.Genie.singular_infiniteInformationRatio_bound
#print axioms ThresholdHC.Genie.singular_informationRatio_bound
#print axioms ThresholdHC.Genie.singular_prefix_gap
#print axioms ThresholdHC.Genie.singular_prefix_information
#print axioms ThresholdHC.Genie.singular_variance_prefix_moment
#print axioms ThresholdHC.Genie.singular_work_prefix
#print axioms ThresholdHC.Genie.stopping_depth_countMean
#print axioms ThresholdHC.Genie.sum_words_by_heads_ennreal
#print axioms ThresholdHC.Genie.tapeParameter
#print axioms ThresholdHC.Genie.tapeParameter_ae
#print axioms ThresholdHC.Genie.tape_parameter_identification
#print axioms ThresholdHC.Genie.terminalInformation
#print axioms ThresholdHC.Genie.terminalInformation_le_latent
#print axioms ThresholdHC.Genie.terminalInformation_tendsto
#print axioms ThresholdHC.Genie.terminal_reveal_sum
#print axioms ThresholdHC.Genie.truncateFlow
#print axioms ThresholdHC.Genie.truncateFlow_cone
#print axioms ThresholdHC.Genie.truncateFlow_intensity
#print axioms ThresholdHC.Genie.truncateFlow_work_le
#print axioms ThresholdHC.Genie.uniformGapLaw
#print axioms ThresholdHC.Genie.uniformGapLaw_probability
#print axioms ThresholdHC.Genie.uniformGap_integral
#print axioms ThresholdHC.Genie.uniformGap_inverse_not_integrable
#print axioms ThresholdHC.Genie.uniformGap_symmetrize
#print axioms ThresholdHC.Genie.uniformMoment
#print axioms ThresholdHC.Genie.uniformMoment_balance
#print axioms ThresholdHC.Genie.uniformMoment_harmonic
#print axioms ThresholdHC.Genie.uniformMoment_nonneg
#print axioms ThresholdHC.Genie.uniformMoment_pos
#print axioms ThresholdHC.Genie.uniformMoment_recurrence
#print axioms ThresholdHC.Genie.uniformMonomial
#print axioms ThresholdHC.Genie.uniformMonomial_continuous
#print axioms ThresholdHC.Genie.uniformSignPrior
#print axioms ThresholdHC.Genie.uniform_gap_prefix_real
#print axioms ThresholdHC.Genie.uniform_prefix_moment
#print axioms ThresholdHC.Genie.uniform_tapeParameter_ae
#print axioms ThresholdHC.Genie.upperSemicontinuous_information_quotient
#print axioms ThresholdHC.Genie.weighted_score
#print axioms ThresholdHC.Genie.weighted_score_square
#print axioms ThresholdHC.StoppingProgram.Admissible
#print axioms ThresholdHC.StoppingProgram.AttainedDualStatement
#print axioms ThresholdHC.StoppingProgram.Certificate
#print axioms ThresholdHC.StoppingProgram.CountState
#print axioms ThresholdHC.StoppingProgram.Feasible
#print axioms ThresholdHC.StoppingProgram.FiniteCertificateStatement
#print axioms ThresholdHC.StoppingProgram.FiniteTailBound
#print axioms ThresholdHC.StoppingProgram.Flow
#print axioms ThresholdHC.StoppingProgram.FlowCone
#print axioms ThresholdHC.StoppingProgram.FlowCone.add
#print axioms ThresholdHC.StoppingProgram.FlowCone.scale
#print axioms ThresholdHC.StoppingProgram.FlowCone.withOutputs
#print axioms ThresholdHC.StoppingProgram.FourPriors
#print axioms ThresholdHC.StoppingProgram.NullPruned
#print axioms ThresholdHC.StoppingProgram.PositiveTable
#print axioms ThresholdHC.StoppingProgram.PriorTuple
#print axioms ThresholdHC.StoppingProgram.ProgramPoint
#print axioms ThresholdHC.StoppingProgram.ProgramUpperStatement
#print axioms ThresholdHC.StoppingProgram.StopTree
#print axioms ThresholdHC.StoppingProgram.abs_le_square_bound
#print axioms ThresholdHC.StoppingProgram.absorbedHigh
#print axioms ThresholdHC.StoppingProgram.absorbedLow
#print axioms ThresholdHC.StoppingProgram.absorbedPriors
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_admissible
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_contrast
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_dualRatio
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_gap
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_informationRatio_le
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_information_le
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_mean_work_ge
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_perspective_le
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_reference
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_variance_ge
#print axioms ThresholdHC.StoppingProgram.absorbedPriors_work_ge
#print axioms ThresholdHC.StoppingProgram.addFlow
#print axioms ThresholdHC.StoppingProgram.affinity_integral_sqrt_overlap
#print axioms ThresholdHC.StoppingProgram.affinity_rms_risk
#print axioms ThresholdHC.StoppingProgram.affinity_sq_le_overlap
#print axioms ThresholdHC.StoppingProgram.affinity_squared_risk
#print axioms ThresholdHC.StoppingProgram.arrayAt
#print axioms ThresholdHC.StoppingProgram.arrayAt_add_flow
#print axioms ThresholdHC.StoppingProgram.arrayAt_continuous
#print axioms ThresholdHC.StoppingProgram.arrayAt_le_of
#print axioms ThresholdHC.StoppingProgram.arrayAt_nonneg
#print axioms ThresholdHC.StoppingProgram.arrayAt_scale_flow
#print axioms ThresholdHC.StoppingProgram.arrayAt_sq
#print axioms ThresholdHC.StoppingProgram.arrayAt_state
#print axioms ThresholdHC.StoppingProgram.arrayAt_zero
#print axioms ThresholdHC.StoppingProgram.arrival_independent_current
#print axioms ThresholdHC.StoppingProgram.attained_four_prior_dual
#print axioms ThresholdHC.StoppingProgram.attained_price_multipliers
#print axioms ThresholdHC.StoppingProgram.bellman
#print axioms ThresholdHC.StoppingProgram.bellmanFlow
#print axioms ThresholdHC.StoppingProgram.bellmanFlow_cone
#print axioms ThresholdHC.StoppingProgram.bellmanFlow_intensity
#print axioms ThresholdHC.StoppingProgram.bellmanFlow_score
#print axioms ThresholdHC.StoppingProgram.bellmanRatio
#print axioms ThresholdHC.StoppingProgram.bellmanRatio_nonneg
#print axioms ThresholdHC.StoppingProgram.bellmanStopProbability
#print axioms ThresholdHC.StoppingProgram.bellmanStopProbability_binary
#print axioms ThresholdHC.StoppingProgram.bellmanStopProbability_complementarity
#print axioms ThresholdHC.StoppingProgram.bellmanStopProbability_root
#print axioms ThresholdHC.StoppingProgram.bellmanStopProbability_terminal
#print axioms ThresholdHC.StoppingProgram.bernoulli_label_floor
#print axioms ThresholdHC.StoppingProgram.bernoulli_label_minimax_floor
#print axioms ThresholdHC.StoppingProgram.biasPolynomial
#print axioms ThresholdHC.StoppingProgram.boundedFirst_eq_iff
#print axioms ThresholdHC.StoppingProgram.bounded_rarity_support_formula
#print axioms ThresholdHC.StoppingProgram.certificateCap
#print axioms ThresholdHC.StoppingProgram.certificateCap_bounds
#print axioms ThresholdHC.StoppingProgram.certificateCap_error
#print axioms ThresholdHC.StoppingProgram.certificateCap_pos
#print axioms ThresholdHC.StoppingProgram.certificatePoint
#print axioms ThresholdHC.StoppingProgram.certificatePoint_mem_domain
#print axioms ThresholdHC.StoppingProgram.certificateSquared
#print axioms ThresholdHC.StoppingProgram.certificate_bias_affine
#print axioms ThresholdHC.StoppingProgram.certificate_lagrange
#print axioms ThresholdHC.StoppingProgram.certificate_realization
#print axioms ThresholdHC.StoppingProgram.choose_pascal_high
#print axioms ThresholdHC.StoppingProgram.choose_pascal_low
#print axioms ThresholdHC.StoppingProgram.compactMaximum
#print axioms ThresholdHC.StoppingProgram.compactMaximum_attained
#print axioms ThresholdHC.StoppingProgram.compactMaximum_convex
#print axioms ThresholdHC.StoppingProgram.compactMaximum_le_iff
#print axioms ThresholdHC.StoppingProgram.compact_minimax_selection
#print axioms ThresholdHC.StoppingProgram.completedStop
#print axioms ThresholdHC.StoppingProgram.completedStop_eq_iff
#print axioms ThresholdHC.StoppingProgram.completedStop_le_cap
#print axioms ThresholdHC.StoppingProgram.completedStop_snoc_le_iff
#print axioms ThresholdHC.StoppingProgram.conePrice
#print axioms ThresholdHC.StoppingProgram.conePrice_information_bound
#print axioms ThresholdHC.StoppingProgram.conePrice_information_finite
#print axioms ThresholdHC.StoppingProgram.conePrice_null_contrast
#print axioms ThresholdHC.StoppingProgram.conePrice_ratio_bound
#print axioms ThresholdHC.StoppingProgram.conePrice_ratio_finite
#print axioms ThresholdHC.StoppingProgram.conePrice_ratio_real_bound
#print axioms ThresholdHC.StoppingProgram.constantCertificate
#print axioms ThresholdHC.StoppingProgram.constantCertificate_feasible
#print axioms ThresholdHC.StoppingProgram.constantPrior
#print axioms ThresholdHC.StoppingProgram.constantPrior_countCoefficient
#print axioms ThresholdHC.StoppingProgram.constantPrior_mean
#print axioms ThresholdHC.StoppingProgram.constantPrior_midpoint
#print axioms ThresholdHC.StoppingProgram.constantPrior_null_state
#print axioms ThresholdHC.StoppingProgram.constant_flowInformation_bound
#print axioms ThresholdHC.StoppingProgram.constant_informationRatio_bound
#print axioms ThresholdHC.StoppingProgram.constant_pair_risk_floor
#print axioms ThresholdHC.StoppingProgram.continuous_bellman
#print axioms ThresholdHC.StoppingProgram.continuous_rootBellman
#print axioms ThresholdHC.StoppingProgram.contractPrior
#print axioms ThresholdHC.StoppingProgram.contractPrior_contrast
#print axioms ThresholdHC.StoppingProgram.contractPrior_gap
#print axioms ThresholdHC.StoppingProgram.contractPrior_information
#print axioms ThresholdHC.StoppingProgram.contractPrior_informationRatio
#print axioms ThresholdHC.StoppingProgram.contractPrior_midpoint
#print axioms ThresholdHC.StoppingProgram.contractPrior_rare
#print axioms ThresholdHC.StoppingProgram.contraction_scale
#print axioms ThresholdHC.StoppingProgram.coordinateMean
#print axioms ThresholdHC.StoppingProgram.coordinateMean_combo_left
#print axioms ThresholdHC.StoppingProgram.coordinateMean_combo_right
#print axioms ThresholdHC.StoppingProgram.countCoefficient
#print axioms ThresholdHC.StoppingProgram.countCoefficient_affine
#print axioms ThresholdHC.StoppingProgram.countCoefficient_dominated
#print axioms ThresholdHC.StoppingProgram.countCoefficient_nonneg
#print axioms ThresholdHC.StoppingProgram.countCoefficient_root
#print axioms ThresholdHC.StoppingProgram.countContrastPolynomial
#print axioms ThresholdHC.StoppingProgram.countContrastPolynomial_eval
#print axioms ThresholdHC.StoppingProgram.countDecision
#print axioms ThresholdHC.StoppingProgram.countDecision_binary
#print axioms ThresholdHC.StoppingProgram.countDecision_complement_hit
#print axioms ThresholdHC.StoppingProgram.countDecision_state
#print axioms ThresholdHC.StoppingProgram.countInformation_eq
#print axioms ThresholdHC.StoppingProgram.countMean
#print axioms ThresholdHC.StoppingProgram.countMeanPolynomial
#print axioms ThresholdHC.StoppingProgram.countMeanPolynomial_eval
#print axioms ThresholdHC.StoppingProgram.countMean_affine
#print axioms ThresholdHC.StoppingProgram.countMean_ge_root
#print axioms ThresholdHC.StoppingProgram.countMean_nonneg
#print axioms ThresholdHC.StoppingProgram.countMean_pruneArray
#print axioms ThresholdHC.StoppingProgram.countMean_raw
#print axioms ThresholdHC.StoppingProgram.countMean_scale
#print axioms ThresholdHC.StoppingProgram.countMean_single
#print axioms ThresholdHC.StoppingProgram.countMean_stop_eq_intensity
#print axioms ThresholdHC.StoppingProgram.countStopProbability
#print axioms ThresholdHC.StoppingProgram.countStopProbability_bounds
#print axioms ThresholdHC.StoppingProgram.countStopProbability_root
#print axioms ThresholdHC.StoppingProgram.creation_population_information
#print axioms ThresholdHC.StoppingProgram.cutoff_prior_decomposition
#print axioms ThresholdHC.StoppingProgram.decisionFactor
#print axioms ThresholdHC.StoppingProgram.decisionFactor_nonneg
#print axioms ThresholdHC.StoppingProgram.decisionFactor_sum
#print axioms ThresholdHC.StoppingProgram.decisionWeight
#print axioms ThresholdHC.StoppingProgram.decisionWeight_join
#print axioms ThresholdHC.StoppingProgram.decisionWeight_match
#print axioms ThresholdHC.StoppingProgram.decisionWeight_nonneg
#print axioms ThresholdHC.StoppingProgram.decisionWeight_product
#print axioms ThresholdHC.StoppingProgram.decisionWeight_single
#print axioms ThresholdHC.StoppingProgram.decisionWeight_sum
#print axioms ThresholdHC.StoppingProgram.decisionWeight_sum_split
#print axioms ThresholdHC.StoppingProgram.density_squared_loss
#print axioms ThresholdHC.StoppingProgram.dualRatio
#print axioms ThresholdHC.StoppingProgram.dualRatio_le_certificate
#print axioms ThresholdHC.StoppingProgram.dualValue
#print axioms ThresholdHC.StoppingProgram.dualValue_le_nine_midpointSquared
#print axioms ThresholdHC.StoppingProgram.enumeratedTable_sum
#print axioms ThresholdHC.StoppingProgram.factored_affinity_nonnegative
#print axioms ThresholdHC.StoppingProgram.feasible_iff_finite_program
#print axioms ThresholdHC.StoppingProgram.feasible_iff_four_cutoffs
#print axioms ThresholdHC.StoppingProgram.feasible_points_closed
#print axioms ThresholdHC.StoppingProgram.feasible_sublevel_bounds
#print axioms ThresholdHC.StoppingProgram.finiteNullMean
#print axioms ThresholdHC.StoppingProgram.finiteNullMean_eq
#print axioms ThresholdHC.StoppingProgram.finiteTailBound_iff
#print axioms ThresholdHC.StoppingProgram.finite_certificate
#print axioms ThresholdHC.StoppingProgram.finite_law_integral
#print axioms ThresholdHC.StoppingProgram.finite_law_tail
#print axioms ThresholdHC.StoppingProgram.finite_population_information
#print axioms ThresholdHC.StoppingProgram.finite_slater_multipliers
#print axioms ThresholdHC.StoppingProgram.finite_word_projection_integral
#print axioms ThresholdHC.StoppingProgram.flowDecisionParameters
#print axioms ThresholdHC.StoppingProgram.flowDecisionParameters_before
#print axioms ThresholdHC.StoppingProgram.flowInformation
#print axioms ThresholdHC.StoppingProgram.flowInformation_finite_of_ratio_finite
#print axioms ThresholdHC.StoppingProgram.flowInformation_finite_prefixes
#print axioms ThresholdHC.StoppingProgram.flowInformation_increments
#print axioms ThresholdHC.StoppingProgram.flowInformation_le_ratio_budget
#print axioms ThresholdHC.StoppingProgram.flowInformation_le_ratio_work
#print axioms ThresholdHC.StoppingProgram.flowInformation_raw
#print axioms ThresholdHC.StoppingProgram.flowInformation_raw_states
#print axioms ThresholdHC.StoppingProgram.flowInformation_scale
#print axioms ThresholdHC.StoppingProgram.flowInformation_toReal_le
#print axioms ThresholdHC.StoppingProgram.flowInformation_toReal_raw
#print axioms ThresholdHC.StoppingProgram.flowInformation_zero_of_intensity_zero
#print axioms ThresholdHC.StoppingProgram.flowPoissonCalls
#print axioms ThresholdHC.StoppingProgram.flowPoissonEstimator
#print axioms ThresholdHC.StoppingProgram.flowPoissonRates
#print axioms ThresholdHC.StoppingProgram.flowPoisson_squaredRisk
#print axioms ThresholdHC.StoppingProgram.flowPoisson_work
#print axioms ThresholdHC.StoppingProgram.flowScore_information
#print axioms ThresholdHC.StoppingProgram.flowScore_le_rootBellman
#print axioms ThresholdHC.StoppingProgram.flowScore_maximum
#print axioms ThresholdHC.StoppingProgram.flowTableOutput
#print axioms ThresholdHC.StoppingProgram.flowTableOutput_mean
#print axioms ThresholdHC.StoppingProgram.flowTableOutput_moment
#print axioms ThresholdHC.StoppingProgram.flowTableRate
#print axioms ThresholdHC.StoppingProgram.flowTableRate_continue
#print axioms ThresholdHC.StoppingProgram.flowTableRate_nonneg
#print axioms ThresholdHC.StoppingProgram.flowTableRate_stop
#print axioms ThresholdHC.StoppingProgram.flowTableRate_sum
#print axioms ThresholdHC.StoppingProgram.flowTableRate_supported
#print axioms ThresholdHC.StoppingProgram.flow_cone_lagrange
#print axioms ThresholdHC.StoppingProgram.flow_continue_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_mixture_arrival
#print axioms ThresholdHC.StoppingProgram.flow_mixture_mean
#print axioms ThresholdHC.StoppingProgram.flow_mixture_probability
#print axioms ThresholdHC.StoppingProgram.flow_mixture_second_moment
#print axioms ThresholdHC.StoppingProgram.flow_mixture_supported_tables
#print axioms ThresholdHC.StoppingProgram.flow_mixture_weights
#print axioms ThresholdHC.StoppingProgram.flow_mixture_work
#print axioms ThresholdHC.StoppingProgram.flow_output_mean
#print axioms ThresholdHC.StoppingProgram.flow_output_second_moment
#print axioms ThresholdHC.StoppingProgram.flow_output_zero_of_stop_zero
#print axioms ThresholdHC.StoppingProgram.flow_potential_bound
#print axioms ThresholdHC.StoppingProgram.flow_stop_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_total_le_intensity
#print axioms ThresholdHC.StoppingProgram.flow_work_ge_intensity
#print axioms ThresholdHC.StoppingProgram.flow_work_stopping_depth
#print axioms ThresholdHC.StoppingProgram.flow_zero_intensity
#print axioms ThresholdHC.StoppingProgram.forcedBellman
#print axioms ThresholdHC.StoppingProgram.forcedBellman_continue
#print axioms ThresholdHC.StoppingProgram.forcedBellman_recursion
#print axioms ThresholdHC.StoppingProgram.forcedBellman_stop
#print axioms ThresholdHC.StoppingProgram.four_prior_multipliers
#print axioms ThresholdHC.StoppingProgram.fractionalUpperPrior
#print axioms ThresholdHC.StoppingProgram.fractionalUpperPrior_decomposition
#print axioms ThresholdHC.StoppingProgram.fractional_cutoff_preserves
#print axioms ThresholdHC.StoppingProgram.fractional_rarity_support
#print axioms ThresholdHC.StoppingProgram.fractional_rarity_support_explicit
#print axioms ThresholdHC.StoppingProgram.fractional_rarity_support_of_memLp
#print axioms ThresholdHC.StoppingProgram.fullCapFlow
#print axioms ThresholdHC.StoppingProgram.fullCapFlow_cone
#print axioms ThresholdHC.StoppingProgram.fullCapFlow_intensity
#print axioms ThresholdHC.StoppingProgram.fullCap_arrayAt
#print axioms ThresholdHC.StoppingProgram.functionMomentImage
#print axioms ThresholdHC.StoppingProgram.functionMomentImage_compact_convex
#print axioms ThresholdHC.StoppingProgram.functionMomentImage_nonempty
#print axioms ThresholdHC.StoppingProgram.gap_tape_prefix_real
#print axioms ThresholdHC.StoppingProgram.headCountMass
#print axioms ThresholdHC.StoppingProgram.headCountMass_add
#print axioms ThresholdHC.StoppingProgram.headCountMass_nonneg
#print axioms ThresholdHC.StoppingProgram.headCountMass_outside
#print axioms ThresholdHC.StoppingProgram.headCountMass_snoc
#print axioms ThresholdHC.StoppingProgram.independent_decision_factor
#print axioms ThresholdHC.StoppingProgram.informationIncrement
#print axioms ThresholdHC.StoppingProgram.informationIncrement_nonneg
#print axioms ThresholdHC.StoppingProgram.informationRatio
#print axioms ThresholdHC.StoppingProgram.informationRatio_bellman
#print axioms ThresholdHC.StoppingProgram.informationRatio_bellman_attained
#print axioms ThresholdHC.StoppingProgram.informationRatio_bellman_zero
#print axioms ThresholdHC.StoppingProgram.informationRatio_finite_iff
#print axioms ThresholdHC.StoppingProgram.informationRatio_finite_of_statewise
#print axioms ThresholdHC.StoppingProgram.informationRatio_increment_identity
#print axioms ThresholdHC.StoppingProgram.informationRatio_le_bellmanRatio
#print axioms ThresholdHC.StoppingProgram.informationRatio_top_iff
#print axioms ThresholdHC.StoppingProgram.integrable_count_mixture
#print axioms ThresholdHC.StoppingProgram.integrable_orderedContinueIndicator
#print axioms ThresholdHC.StoppingProgram.integrable_orderedStopIndicator
#print axioms ThresholdHC.StoppingProgram.integrable_overlapDensity
#print axioms ThresholdHC.StoppingProgram.integrable_prior_function
#print axioms ThresholdHC.StoppingProgram.integrable_sign_prior
#print axioms ThresholdHC.StoppingProgram.intensity
#print axioms ThresholdHC.StoppingProgram.intensity_scale
#print axioms ThresholdHC.StoppingProgram.joinDecision
#print axioms ThresholdHC.StoppingProgram.joinDecision_other
#print axioms ThresholdHC.StoppingProgram.joinDecision_self
#print axioms ThresholdHC.StoppingProgram.joinDecision_update
#print axioms ThresholdHC.StoppingProgram.le_compactMaximum
#print axioms ThresholdHC.StoppingProgram.le_priceValue
#print axioms ThresholdHC.StoppingProgram.le_ratioValue
#print axioms ThresholdHC.StoppingProgram.levelAverage
#print axioms ThresholdHC.StoppingProgram.levelAverage_properties
#print axioms ThresholdHC.StoppingProgram.levelPriorMass
#print axioms ThresholdHC.StoppingProgram.levelPriorMass_bounds
#print axioms ThresholdHC.StoppingProgram.linear_lower_bound_forces_zero
#print axioms ThresholdHC.StoppingProgram.linear_pi_expansion
#print axioms ThresholdHC.StoppingProgram.linear_ray_lower_bound_forces_nonneg
#print axioms ThresholdHC.StoppingProgram.measurable_completedStop
#print axioms ThresholdHC.StoppingProgram.measurable_orderedContinueIndicator
#print axioms ThresholdHC.StoppingProgram.measurable_orderedStopIndicator
#print axioms ThresholdHC.StoppingProgram.measurable_overlapDensity
#print axioms ThresholdHC.StoppingProgram.measurable_prefixTruncation
#print axioms ThresholdHC.StoppingProgram.midpointFourPriors
#print axioms ThresholdHC.StoppingProgram.midpointFourPriors_admissible
#print axioms ThresholdHC.StoppingProgram.midpointPrior
#print axioms ThresholdHC.StoppingProgram.midpointPrior_comm
#print axioms ThresholdHC.StoppingProgram.midpointPrior_countCoefficient
#print axioms ThresholdHC.StoppingProgram.midpointPrior_mean
#print axioms ThresholdHC.StoppingProgram.midpointSquared
#print axioms ThresholdHC.StoppingProgram.midpointSquared_le_dualValue
#print axioms ThresholdHC.StoppingProgram.midpointValue
#print axioms ThresholdHC.StoppingProgram.midpoint_comparison
#print axioms ThresholdHC.StoppingProgram.midpoint_dual_root
#print axioms ThresholdHC.StoppingProgram.midpoint_informationRatio_finite
#print axioms ThresholdHC.StoppingProgram.midpoint_prefixCoefficient
#print axioms ThresholdHC.StoppingProgram.midpoint_prefixInformation_finite
#print axioms ThresholdHC.StoppingProgram.midpoint_prefixReward
#print axioms ThresholdHC.StoppingProgram.midpoint_quadratic_hellinger
#print axioms ThresholdHC.StoppingProgram.minimax_le_certificate
#print axioms ThresholdHC.StoppingProgram.minimax_le_program
#print axioms ThresholdHC.StoppingProgram.mixPrior
#print axioms ThresholdHC.StoppingProgram.mixPrior_countCoefficient
#print axioms ThresholdHC.StoppingProgram.mixPrior_integral
#print axioms ThresholdHC.StoppingProgram.mixPrior_mean
#print axioms ThresholdHC.StoppingProgram.mixPrior_rare
#print axioms ThresholdHC.StoppingProgram.mixture_arrival_continue
#print axioms ThresholdHC.StoppingProgram.mixture_arrival_stop
#print axioms ThresholdHC.StoppingProgram.mixture_policyArrival
#print axioms ThresholdHC.StoppingProgram.momentCoordinateBound
#print axioms ThresholdHC.StoppingProgram.normalizedRawFlow
#print axioms ThresholdHC.StoppingProgram.normalizedRawFlow_cone
#print axioms ThresholdHC.StoppingProgram.normalizedRawFlow_intensity
#print axioms ThresholdHC.StoppingProgram.normalized_flow
#print axioms ThresholdHC.StoppingProgram.nullPruned_points_closed
#print axioms ThresholdHC.StoppingProgram.observable_prefix_information
#print axioms ThresholdHC.StoppingProgram.observable_prefix_information_budget
#print axioms ThresholdHC.StoppingProgram.observable_prefix_risk
#print axioms ThresholdHC.StoppingProgram.offsetCoordinateBound
#print axioms ThresholdHC.StoppingProgram.optimalTree
#print axioms ThresholdHC.StoppingProgram.optimalTree_score
#print axioms ThresholdHC.StoppingProgram.optimizedOutput
#print axioms ThresholdHC.StoppingProgram.optimizedOutput_cone
#print axioms ThresholdHC.StoppingProgram.optimizedOutput_lagrange
#print axioms ThresholdHC.StoppingProgram.optimized_perspective_identity
#print axioms ThresholdHC.StoppingProgram.orderedContinueIndicator
#print axioms ThresholdHC.StoppingProgram.orderedContinueMass
#print axioms ThresholdHC.StoppingProgram.orderedCountContinue
#print axioms ThresholdHC.StoppingProgram.orderedCountStop
#print axioms ThresholdHC.StoppingProgram.orderedFlow
#print axioms ThresholdHC.StoppingProgram.orderedFlow_actual_work
#print axioms ThresholdHC.StoppingProgram.orderedFlow_cone
#print axioms ThresholdHC.StoppingProgram.orderedFlow_information
#print axioms ThresholdHC.StoppingProgram.orderedFlow_midpoint_hellinger
#print axioms ThresholdHC.StoppingProgram.orderedFlow_stopped_rewards
#print axioms ThresholdHC.StoppingProgram.orderedFlow_work_moment
#print axioms ThresholdHC.StoppingProgram.orderedStopIndicator
#print axioms ThresholdHC.StoppingProgram.orderedStopMass
#print axioms ThresholdHC.StoppingProgram.orderedStopMass_eq
#print axioms ThresholdHC.StoppingProgram.ordered_indicator_bounds
#print axioms ThresholdHC.StoppingProgram.ordered_indicator_conservation
#print axioms ThresholdHC.StoppingProgram.ordered_indicator_terminal
#print axioms ThresholdHC.StoppingProgram.ordered_mass_conservation
#print axioms ThresholdHC.StoppingProgram.ordered_stopped_hellinger_work
#print axioms ThresholdHC.StoppingProgram.original_path_valid
#print axioms ThresholdHC.StoppingProgram.original_stopped_word_affinity
#print axioms ThresholdHC.StoppingProgram.original_stopped_word_integral
#print axioms ThresholdHC.StoppingProgram.original_stopped_word_mass
#print axioms ThresholdHC.StoppingProgram.original_work_stopped_integral
#print axioms ThresholdHC.StoppingProgram.outputCoordinateBound
#print axioms ThresholdHC.StoppingProgram.overlapDensity
#print axioms ThresholdHC.StoppingProgram.overlapDensity_le_one
#print axioms ThresholdHC.StoppingProgram.overlapDensity_nonneg
#print axioms ThresholdHC.StoppingProgram.pascal_weights_sum
#print axioms ThresholdHC.StoppingProgram.perspective
#print axioms ThresholdHC.StoppingProgram.perspectiveCone_add
#print axioms ThresholdHC.StoppingProgram.perspective_add_le
#print axioms ThresholdHC.StoppingProgram.perspective_antitone_reference
#print axioms ThresholdHC.StoppingProgram.perspective_cone_attains
#print axioms ThresholdHC.StoppingProgram.perspective_cone_lower
#print axioms ThresholdHC.StoppingProgram.perspective_cone_lower_toReal
#print axioms ThresholdHC.StoppingProgram.perspective_finite_iff
#print axioms ThresholdHC.StoppingProgram.perspective_label_bound
#print axioms ThresholdHC.StoppingProgram.perspective_nonzero_zero
#print axioms ThresholdHC.StoppingProgram.perspective_pos
#print axioms ThresholdHC.StoppingProgram.perspective_scale
#print axioms ThresholdHC.StoppingProgram.perspective_scale_contrast
#print axioms ThresholdHC.StoppingProgram.perspective_toReal_eq
#print axioms ThresholdHC.StoppingProgram.perspective_zero_zero
#print axioms ThresholdHC.StoppingProgram.pointCertificate
#print axioms ThresholdHC.StoppingProgram.pointCertificate_certificatePoint
#print axioms ThresholdHC.StoppingProgram.pointFlow
#print axioms ThresholdHC.StoppingProgram.pointFlow_combo
#print axioms ThresholdHC.StoppingProgram.pointFlow_cone_closed
#print axioms ThresholdHC.StoppingProgram.pointFlow_cone_iff
#print axioms ThresholdHC.StoppingProgram.pointObjective
#print axioms ThresholdHC.StoppingProgram.pointObjective_continuous
#print axioms ThresholdHC.StoppingProgram.pointObjective_convex
#print axioms ThresholdHC.StoppingProgram.pointResidual
#print axioms ThresholdHC.StoppingProgram.pointResidual_combo_point
#print axioms ThresholdHC.StoppingProgram.pointResidual_combo_prior
#print axioms ThresholdHC.StoppingProgram.pointResidual_continuous_point
#print axioms ThresholdHC.StoppingProgram.pointResidual_continuous_prior
#print axioms ThresholdHC.StoppingProgram.point_feasible_iff
#print axioms ThresholdHC.StoppingProgram.poissonPlan_unscaled_squaredRisk
#print axioms ThresholdHC.StoppingProgram.policyArrival
#print axioms ThresholdHC.StoppingProgram.policyArrival_congr_before
#print axioms ThresholdHC.StoppingProgram.policyArrival_eq_raw
#print axioms ThresholdHC.StoppingProgram.policyArrival_mul
#print axioms ThresholdHC.StoppingProgram.policyArrival_nonneg
#print axioms ThresholdHC.StoppingProgram.policyArrival_outside
#print axioms ThresholdHC.StoppingProgram.policyFlow
#print axioms ThresholdHC.StoppingProgram.policyFlow_cone
#print axioms ThresholdHC.StoppingProgram.policyFlow_intensity
#print axioms ThresholdHC.StoppingProgram.policy_weights_realize_flow
#print axioms ThresholdHC.StoppingProgram.polynomialTail
#print axioms ThresholdHC.StoppingProgram.population_prefix_integrable
#print axioms ThresholdHC.StoppingProgram.population_prefix_integral
#print axioms ThresholdHC.StoppingProgram.population_tape_prefix_real
#print axioms ThresholdHC.StoppingProgram.population_word_integral
#print axioms ThresholdHC.StoppingProgram.positiveTable_enumeration
#print axioms ThresholdHC.StoppingProgram.positiveTable_nonempty
#print axioms ThresholdHC.StoppingProgram.positiveTable_sum
#print axioms ThresholdHC.StoppingProgram.positive_decision_one
#print axioms ThresholdHC.StoppingProgram.positive_decision_zero
#print axioms ThresholdHC.StoppingProgram.positive_dual_witness
#print axioms ThresholdHC.StoppingProgram.prefixCoefficient
#print axioms ThresholdHC.StoppingProgram.prefixCoefficient_add
#print axioms ThresholdHC.StoppingProgram.prefixCoefficient_nonneg
#print axioms ThresholdHC.StoppingProgram.prefixCoefficient_root
#print axioms ThresholdHC.StoppingProgram.prefixInformation
#print axioms ThresholdHC.StoppingProgram.prefixInformation_children
#print axioms ThresholdHC.StoppingProgram.prefixInformation_finite_of_ratio
#print axioms ThresholdHC.StoppingProgram.prefixInformation_finite_of_terminal
#print axioms ThresholdHC.StoppingProgram.prefixInformation_root
#print axioms ThresholdHC.StoppingProgram.prefixInformation_top_iff
#print axioms ThresholdHC.StoppingProgram.prefixLikelihood
#print axioms ThresholdHC.StoppingProgram.prefixLikelihood_add
#print axioms ThresholdHC.StoppingProgram.prefixLikelihood_nonneg
#print axioms ThresholdHC.StoppingProgram.prefixReward
#print axioms ThresholdHC.StoppingProgram.prefixTruncation
#print axioms ThresholdHC.StoppingProgram.prefixTruncation_ennreal_loss
#print axioms ThresholdHC.StoppingProgram.prefixTruncation_loss
#print axioms ThresholdHC.StoppingProgram.prefixTruncation_rmsRisk
#print axioms ThresholdHC.StoppingProgram.prefixTruncation_squaredRisk
#print axioms ThresholdHC.StoppingProgram.prefix_lower_transfer
#print axioms ThresholdHC.StoppingProgram.prefix_pair_modulus
#print axioms ThresholdHC.StoppingProgram.prefix_program_bound
#print axioms ThresholdHC.StoppingProgram.priceValue
#print axioms ThresholdHC.StoppingProgram.priceValue_at_ratio
#print axioms ThresholdHC.StoppingProgram.priceValue_attained
#print axioms ThresholdHC.StoppingProgram.priceValue_le_zero_iff
#print axioms ThresholdHC.StoppingProgram.priceValue_strictAnti
#print axioms ThresholdHC.StoppingProgram.priceValue_zero_iff
#print axioms ThresholdHC.StoppingProgram.priorCoordinates
#print axioms ThresholdHC.StoppingProgram.priorMomentImage
#print axioms ThresholdHC.StoppingProgram.priorMomentImage_compact_convex
#print axioms ThresholdHC.StoppingProgram.priorMomentImage_mem
#print axioms ThresholdHC.StoppingProgram.priorMomentImage_nonempty
#print axioms ThresholdHC.StoppingProgram.priorTupleSet
#print axioms ThresholdHC.StoppingProgram.prior_excess_integral
#print axioms ThresholdHC.StoppingProgram.prior_excess_le_positive
#print axioms ThresholdHC.StoppingProgram.prior_function_le_rareFunctional
#print axioms ThresholdHC.StoppingProgram.prior_function_upper_tail
#print axioms ThresholdHC.StoppingProgram.programDomain
#print axioms ThresholdHC.StoppingProgram.programDomain_closed
#print axioms ThresholdHC.StoppingProgram.programDomain_convex
#print axioms ThresholdHC.StoppingProgram.programSquared
#print axioms ThresholdHC.StoppingProgram.programSquared_attained
#print axioms ThresholdHC.StoppingProgram.programSquared_finite
#print axioms ThresholdHC.StoppingProgram.programSquared_le_constant
#print axioms ThresholdHC.StoppingProgram.programSquared_pos
#print axioms ThresholdHC.StoppingProgram.programValue
#print axioms ThresholdHC.StoppingProgram.program_le_minimax_truncation
#print axioms ThresholdHC.StoppingProgram.program_le_risk_truncation
#print axioms ThresholdHC.StoppingProgram.program_multipliers
#print axioms ThresholdHC.StoppingProgram.program_point_lower
#print axioms ThresholdHC.StoppingProgram.program_strict_inequalities
#print axioms ThresholdHC.StoppingProgram.program_upper
#print axioms ThresholdHC.StoppingProgram.pruneArray
#print axioms ThresholdHC.StoppingProgram.pruneCertificate
#print axioms ThresholdHC.StoppingProgram.pruneCertificate_feasible
#print axioms ThresholdHC.StoppingProgram.pruneCertificate_pruned
#print axioms ThresholdHC.StoppingProgram.pruneFlow
#print axioms ThresholdHC.StoppingProgram.pruneFlow_cone
#print axioms ThresholdHC.StoppingProgram.prunedSublevel
#print axioms ThresholdHC.StoppingProgram.prunedSublevel_box
#print axioms ThresholdHC.StoppingProgram.prunedSublevel_closed
#print axioms ThresholdHC.StoppingProgram.prunedSublevel_compact
#print axioms ThresholdHC.StoppingProgram.quadratic_div_add_le
#print axioms ThresholdHC.StoppingProgram.randomized_price_le
#print axioms ThresholdHC.StoppingProgram.rareFunctional
#print axioms ThresholdHC.StoppingProgram.rareFunctional_attained
#print axioms ThresholdHC.StoppingProgram.rareFunctional_eq_sSup
#print axioms ThresholdHC.StoppingProgram.rareFunctional_upper_tail
#print axioms ThresholdHC.StoppingProgram.rareMomentSet
#print axioms ThresholdHC.StoppingProgram.rareMomentSet_compact_convex
#print axioms ThresholdHC.StoppingProgram.rareMomentSet_eq_half_image
#print axioms ThresholdHC.StoppingProgram.rarity_function_multiplier
#print axioms ThresholdHC.StoppingProgram.rarity_support_formula
#print axioms ThresholdHC.StoppingProgram.rarity_support_formula_bounded_above
#print axioms ThresholdHC.StoppingProgram.ratioValue
#print axioms ThresholdHC.StoppingProgram.ratioValue_attained
#print axioms ThresholdHC.StoppingProgram.ratioValue_nonneg
#print axioms ThresholdHC.StoppingProgram.rawArray
#print axioms ThresholdHC.StoppingProgram.rawArray_mul
#print axioms ThresholdHC.StoppingProgram.rawArray_nonneg
#print axioms ThresholdHC.StoppingProgram.rawArray_outside
#print axioms ThresholdHC.StoppingProgram.rawArray_terminal
#print axioms ThresholdHC.StoppingProgram.rawChildren
#print axioms ThresholdHC.StoppingProgram.rawFlowScore
#print axioms ThresholdHC.StoppingProgram.rawLayer
#print axioms ThresholdHC.StoppingProgram.rawLayer_countMean
#print axioms ThresholdHC.StoppingProgram.rawLayer_depth_weight
#print axioms ThresholdHC.StoppingProgram.rawLayer_mul_depth
#print axioms ThresholdHC.StoppingProgram.raw_continue_fraction
#print axioms ThresholdHC.StoppingProgram.raw_flow_recursion
#print axioms ThresholdHC.StoppingProgram.raw_layer_conservation
#print axioms ThresholdHC.StoppingProgram.raw_normalizedRawFlow_continue
#print axioms ThresholdHC.StoppingProgram.raw_normalizedRawFlow_stop
#print axioms ThresholdHC.StoppingProgram.raw_policyFlow_continue
#print axioms ThresholdHC.StoppingProgram.raw_policyFlow_stop
#print axioms ThresholdHC.StoppingProgram.raw_root_total
#print axioms ThresholdHC.StoppingProgram.raw_stop_fraction
#print axioms ThresholdHC.StoppingProgram.raw_weighted_telescope
#print axioms ThresholdHC.StoppingProgram.robustResidual
#print axioms ThresholdHC.StoppingProgram.robustResidual_convex
#print axioms ThresholdHC.StoppingProgram.robustResidual_nonpos_iff
#print axioms ThresholdHC.StoppingProgram.robust_polynomial_bound_iff
#print axioms ThresholdHC.StoppingProgram.rootBellman
#print axioms ThresholdHC.StoppingProgram.rootBellman_eq_priceValue
#print axioms ThresholdHC.StoppingProgram.rootBellman_maximum
#print axioms ThresholdHC.StoppingProgram.rootBellman_strictAnti
#print axioms ThresholdHC.StoppingProgram.rootBellman_zero_iff
#print axioms ThresholdHC.StoppingProgram.rootInformation
#print axioms ThresholdHC.StoppingProgram.rootState
#print axioms ThresholdHC.StoppingProgram.rootWork
#print axioms ThresholdHC.StoppingProgram.rootWork_bounds
#print axioms ThresholdHC.StoppingProgram.scaleFlow
#print axioms ThresholdHC.StoppingProgram.shiftEstimator
#print axioms ThresholdHC.StoppingProgram.shiftEstimator_experiment
#print axioms ThresholdHC.StoppingProgram.shiftEstimator_squaredRisk
#print axioms ThresholdHC.StoppingProgram.shiftEstimator_work
#print axioms ThresholdHC.StoppingProgram.shortWord
#print axioms ThresholdHC.StoppingProgram.shortWord_self
#print axioms ThresholdHC.StoppingProgram.shortWord_snoc
#print axioms ThresholdHC.StoppingProgram.shortWord_tapePrefix
#print axioms ThresholdHC.StoppingProgram.singleOutput
#print axioms ThresholdHC.StoppingProgram.singleOutput_cone
#print axioms ThresholdHC.StoppingProgram.squared_bias_bound
#print axioms ThresholdHC.StoppingProgram.squared_loss_overlap_integral
#print axioms ThresholdHC.StoppingProgram.state_eq_root
#print axioms ThresholdHC.StoppingProgram.stopTree_fintype
#print axioms ThresholdHC.StoppingProgram.stopTree_nonempty
#print axioms ThresholdHC.StoppingProgram.stoppedHellinger
#print axioms ThresholdHC.StoppingProgram.stoppedHellinger_squares
#print axioms ThresholdHC.StoppingProgram.stoppedReferenceSum
#print axioms ThresholdHC.StoppingProgram.stoppedReferenceSum_total
#print axioms ThresholdHC.StoppingProgram.strong_four_prior_duality
#print axioms ThresholdHC.StoppingProgram.sum_words_by_heads
#print axioms ThresholdHC.StoppingProgram.tableCall
#print axioms ThresholdHC.StoppingProgram.tableCall_cost_le
#print axioms ThresholdHC.StoppingProgram.tableCost
#print axioms ThresholdHC.StoppingProgram.tableCost_eq_iff
#print axioms ThresholdHC.StoppingProgram.tableCost_ge_iff
#print axioms ThresholdHC.StoppingProgram.tableCost_integral
#print axioms ThresholdHC.StoppingProgram.tableCost_positive
#print axioms ThresholdHC.StoppingProgram.tableCost_word_expansion
#print axioms ThresholdHC.StoppingProgram.tableDecision_at_stop
#print axioms ThresholdHC.StoppingProgram.tableHit
#print axioms ThresholdHC.StoppingProgram.tableStoppedState
#print axioms ThresholdHC.StoppingProgram.tableValue
#print axioms ThresholdHC.StoppingProgram.tableValue_bounded
#print axioms ThresholdHC.StoppingProgram.tableValue_eq
#print axioms ThresholdHC.StoppingProgram.tableValue_full_prefix
#print axioms ThresholdHC.StoppingProgram.tableValue_integral
#print axioms ThresholdHC.StoppingProgram.tableValue_integral_full_prefix
#print axioms ThresholdHC.StoppingProgram.tableValue_second_moment
#print axioms ThresholdHC.StoppingProgram.tableValue_sq
#print axioms ThresholdHC.StoppingProgram.tableValue_word_expansion
#print axioms ThresholdHC.StoppingProgram.treeInformation
#print axioms ThresholdHC.StoppingProgram.treeInformation_nonneg
#print axioms ThresholdHC.StoppingProgram.treeScore
#print axioms ThresholdHC.StoppingProgram.treeScore_eq
#print axioms ThresholdHC.StoppingProgram.treeScore_le_bellman
#print axioms ThresholdHC.StoppingProgram.treeWork
#print axioms ThresholdHC.StoppingProgram.treeWork_le
#print axioms ThresholdHC.StoppingProgram.treeWork_nonneg
#print axioms ThresholdHC.StoppingProgram.truncation_error_tendsto
#print axioms ThresholdHC.StoppingProgram.tupleLagrangian
#print axioms ThresholdHC.StoppingProgram.tupleLagrangian_concave
#print axioms ThresholdHC.StoppingProgram.tupleLagrangian_continuous_point
#print axioms ThresholdHC.StoppingProgram.tupleLagrangian_continuous_prior
#print axioms ThresholdHC.StoppingProgram.tupleLagrangian_convex
#print axioms ThresholdHC.StoppingProgram.tuple_multipliers
#print axioms ThresholdHC.StoppingProgram.upperLevelPrior
#print axioms ThresholdHC.StoppingProgram.upperLevelPrior_excess
#print axioms ThresholdHC.StoppingProgram.upper_tail_equality_cutoff
#print axioms ThresholdHC.StoppingProgram.valid_path_continuation_work
#print axioms ThresholdHC.StoppingProgram.valid_path_halt_reconstruction
#print axioms ThresholdHC.StoppingProgram.weak_duality
#print axioms ThresholdHC.StoppingProgram.withOutputs
#print axioms ThresholdHC.StoppingProgram.wordArrival
#print axioms ThresholdHC.StoppingProgram.wordArrivalCount
#print axioms ThresholdHC.StoppingProgram.wordArrivalCount_eq_policyArrival
#print axioms ThresholdHC.StoppingProgram.wordArrivalCount_succ
#print axioms ThresholdHC.StoppingProgram.wordArrivalCount_zero
#print axioms ThresholdHC.StoppingProgram.wordArrival_snoc
#print axioms ThresholdHC.StoppingProgram.wordArrival_tape_indicator
#print axioms ThresholdHC.StoppingProgram.wordContinue_tape_indicator
#print axioms ThresholdHC.StoppingProgram.wordHeads_le_length
#print axioms ThresholdHC.StoppingProgram.wordHeads_snoc
#print axioms ThresholdHC.StoppingProgram.wordHeads_sum
#print axioms ThresholdHC.StoppingProgram.wordStop_tape_indicator
#print axioms ThresholdHC.StoppingProgram.zeroFlow
#print axioms ThresholdHC.StoppingProgram.zeroFlow_cone
