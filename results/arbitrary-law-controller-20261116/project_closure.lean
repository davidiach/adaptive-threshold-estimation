import ThresholdHC.Anytime.Compatibility
import ThresholdHC.Anytime.Coverage
import ThresholdHC.Anytime.Full
import ThresholdHC.Anytime.IntervalAlgebra
import ThresholdHC.Anytime.Intervals
import ThresholdHC.Anytime.KnownStages
import ThresholdHC.Anytime.Local
import ThresholdHC.Anytime.Schedule
import ThresholdHC.Anytime.Spending
import ThresholdHC.Anytime.Width
import ThresholdHC.ArbitraryLawAdaptation.BandGeometry
import ThresholdHC.ArbitraryLawAdaptation.BandPenalty
import ThresholdHC.ArbitraryLawAdaptation.CDFCoupling
import ThresholdHC.ArbitraryLawAdaptation.CDFEnvelope
import ThresholdHC.ArbitraryLawAdaptation.CDFSelection
import ThresholdHC.ArbitraryLawAdaptation.CountableEntropy
import ThresholdHC.ArbitraryLawAdaptation.CountableTransport
import ThresholdHC.ArbitraryLawAdaptation.CouplingEntropy
import ThresholdHC.ArbitraryLawAdaptation.DominatedMass
import ThresholdHC.ArbitraryLawAdaptation.DominatedSelection
import ThresholdHC.ArbitraryLawAdaptation.EntropyTransport
import ThresholdHC.ArbitraryLawAdaptation.GammaTransport
import ThresholdHC.ArbitraryLawAdaptation.IncreasingSelection
import ThresholdHC.ArbitraryLawAdaptation.LearnedCDF
import ThresholdHC.ArbitraryLawAdaptation.LearnedOracle
import ThresholdHC.ArbitraryLawAdaptation.LearnedStage
import ThresholdHC.ArbitraryLawAdaptation.LightContraction
import ThresholdHC.ArbitraryLawAdaptation.LightContractionCells
import ThresholdHC.ArbitraryLawAdaptation.LightContractionConstants
import ThresholdHC.ArbitraryLawAdaptation.LightContractionGeometry
import ThresholdHC.ArbitraryLawAdaptation.LightContractionTail
import ThresholdHC.ArbitraryLawAdaptation.LightMultiplier
import ThresholdHC.ArbitraryLawAdaptation.PilotOnset
import ThresholdHC.ArbitraryLawAdaptation.ProductEntropy
import ThresholdHC.ArbitraryLawAdaptation.SelectionLift
import ThresholdHC.ArbitraryLawAdaptation.TailBlockReader
import ThresholdHC.ArbitraryLawAdaptation.TailMedian
import ThresholdHC.ArbitraryLawAdaptation.TailMedianLaw
import ThresholdHC.ArbitraryLawAdaptation.TailMedianProbability
import ThresholdHC.ArbitraryLawAdaptation.TailObservable
import ThresholdHC.ArbitraryLawAdaptation.TailOracle
import ThresholdHC.ArbitraryLawAdaptation.TailOracleLaw
import ThresholdHC.ArbitraryLawAdaptation.TailPilot
import ThresholdHC.ArbitraryLawAdaptation.TailPilotLaw
import ThresholdHC.ArbitraryLawAdaptation.TailProbe
import ThresholdHC.ArbitraryLawAdaptation.TailProbeLaw
import ThresholdHC.ArbitraryLawAdaptation.TailProbeProbability
import ThresholdHC.ArbitraryLawAdaptation.TailProbeReader
import ThresholdHC.ArbitraryLawAdaptation.TailTest
import ThresholdHC.ArbitraryLawAdaptation.TailTestLaw
import ThresholdHC.ArbitraryLawAdaptation.TailTestProbability
import ThresholdHC.ArbitraryLawAdaptation.TransportCells
import ThresholdHC.ArbitraryLawAdaptation.ZeroAlgebra
import ThresholdHC.ArbitraryLawAdaptation.ZeroCoupling
import ThresholdHC.ArbitraryLawAdaptation.ZeroModel
import ThresholdHC.ArbitraryLawAdaptation.ZeroQuantile
import ThresholdHC.ArbitraryLawAdaptation.ZeroSelection
import ThresholdHC.ArbitraryLawController.Budget
import ThresholdHC.ArbitraryLawController.Coverage
import ThresholdHC.ArbitraryLawController.Execution
import ThresholdHC.ArbitraryLawController.Full
import ThresholdHC.ArbitraryLawController.Intervals
import ThresholdHC.ArbitraryLawController.JointFailure
import ThresholdHC.ArbitraryLawController.LogSchedule
import ThresholdHC.ArbitraryLawController.Onset
import ThresholdHC.ArbitraryLawController.Rate
import ThresholdHC.ArbitraryLawController.Schedule
import ThresholdHC.ArbitraryLawController.Stages
import ThresholdHC.ArbitraryLawController.ZeroScale
import ThresholdHC.BlindUpper.ActualBatch
import ThresholdHC.BlindUpper.BatchMachine
import ThresholdHC.BlindUpper.BatchPath
import ThresholdHC.BlindUpper.BatchRealization
import ThresholdHC.BlindUpper.BudgetChoice
import ThresholdHC.BlindUpper.CalibrationBundle
import ThresholdHC.BlindUpper.CallConsumes
import ThresholdHC.BlindUpper.CallExecution
import ThresholdHC.BlindUpper.CallLaw
import ThresholdHC.BlindUpper.CallObservation
import ThresholdHC.BlindUpper.CallPlan
import ThresholdHC.BlindUpper.ClassifierProcedure
import ThresholdHC.BlindUpper.ControllerExecution
import ThresholdHC.BlindUpper.ControllerOutput
import ThresholdHC.BlindUpper.CutoffBatch
import ThresholdHC.BlindUpper.CutoffBiasWork
import ThresholdHC.BlindUpper.CutoffBounds
import ThresholdHC.BlindUpper.CutoffModulus
import ThresholdHC.BlindUpper.CutoffMoments
import ThresholdHC.BlindUpper.CutoffProcedure
import ThresholdHC.BlindUpper.DoubleGeometric
import ThresholdHC.BlindUpper.FiniteProcedure
import ThresholdHC.BlindUpper.FirstSuccess
import ThresholdHC.BlindUpper.Full
import ThresholdHC.BlindUpper.InfiniteArrays
import ThresholdHC.BlindUpper.MachinePath
import ThresholdHC.BlindUpper.MarkedCall
import ThresholdHC.BlindUpper.MixedProduction
import ThresholdHC.BlindUpper.PaddedCall
import ThresholdHC.BlindUpper.PhasePlan
import ThresholdHC.BlindUpper.PilotCost
import ThresholdHC.BlindUpper.PilotCount
import ThresholdHC.BlindUpper.PilotWork
import ThresholdHC.BlindUpper.PopulationBounds
import ThresholdHC.BlindUpper.PopulationMean
import ThresholdHC.BlindUpper.ProductionAverage
import ThresholdHC.BlindUpper.ProductionCost
import ThresholdHC.BlindUpper.SeedInput
import ThresholdHC.BlindUpper.Specification
import ThresholdHC.BlindUpper.TerminalOutput
import ThresholdHC.CapIdentification.CenteredBasis
import ThresholdHC.CapIdentification.ContrastFunctional
import ThresholdHC.CapIdentification.CountBounds
import ThresholdHC.CapIdentification.CountMatching
import ThresholdHC.CapIdentification.FullCapCertificate
import ThresholdHC.CapIdentification.Interpolation
import ThresholdHC.CapIdentification.MomentCoordinates
import ThresholdHC.CapIdentification.OddPolynomials
import ThresholdHC.CapIdentification.PolynomialL2
import ThresholdHC.CapIdentification.PrefixBasis
import ThresholdHC.CapIdentification.PrefixRepresentation
import ThresholdHC.CapIdentification.StoppedMatching
import ThresholdHC.CapIdentification.TerminalMoments
import ThresholdHC.Confidence.Amplification
import ThresholdHC.Confidence.BatchLift
import ThresholdHC.Confidence.BatchSequence
import ThresholdHC.Confidence.BudgetScale
import ThresholdHC.Confidence.Controller
import ThresholdHC.Confidence.Execution
import ThresholdHC.Confidence.Full
import ThresholdHC.Confidence.Information
import ThresholdHC.Confidence.InputLaw
import ThresholdHC.Confidence.Lower
import ThresholdHC.Confidence.Median
import ThresholdHC.Confidence.Model
import ThresholdHC.Confidence.Nonvacuity
import ThresholdHC.Confidence.Pointwise
import ThresholdHC.Confidence.Realization
import ThresholdHC.Confidence.SingleFailure
import ThresholdHC.Confidence.Specification
import ThresholdHC.Confidence.Testing
import ThresholdHC.ConfidenceProgram.Amplify
import ThresholdHC.ConfidenceProgram.Blocks
import ThresholdHC.ConfidenceProgram.Lower
import ThresholdHC.ConfidenceProgram.Majority
import ThresholdHC.ConfidenceProgram.MedianController
import ThresholdHC.ConfidenceProgram.Midpoint
import ThresholdHC.ConfidenceProgram.Schedule
import ThresholdHC.ConfidenceProgram.Single
import ThresholdHC.ConfidenceProgram.Upper
import ThresholdHC.ConfidenceTransfer.CommonPairRate
import ThresholdHC.ConfidenceTransfer.Creation
import ThresholdHC.ConfidenceTransfer.CriticalModel
import ThresholdHC.ConfidenceTransfer.CriticalRate
import ThresholdHC.ConfidenceTransfer.FiniteTransfer
import ThresholdHC.ConfidenceTransfer.Hybrid
import ThresholdHC.ConfidenceTransfer.Observable
import ThresholdHC.ConfidenceTransfer.Quarter
import ThresholdHC.ConfidenceTransfer.Specification
import ThresholdHC.ConfidenceTransfer.Terminal
import ThresholdHC.ConfidenceTransfer.Testing
import ThresholdHC.CriticalAllSizes.SingleGap
import ThresholdHC.CriticalEntropy.Activation
import ThresholdHC.CriticalEntropy.ActivationCost
import ThresholdHC.CriticalEntropy.ActivationModel
import ThresholdHC.CriticalEntropy.AffinityTesting
import ThresholdHC.CriticalEntropy.BaseCost
import ThresholdHC.CriticalEntropy.BernoulliPrefix
import ThresholdHC.CriticalEntropy.CapInvariance
import ThresholdHC.CriticalEntropy.CappedObservation
import ThresholdHC.CriticalEntropy.CommonPoint
import ThresholdHC.CriticalEntropy.ConditionalMoments
import ThresholdHC.CriticalEntropy.CreationPopulation
import ThresholdHC.CriticalEntropy.CriticalAlgorithmLower
import ThresholdHC.CriticalEntropy.CriticalAnnuli
import ThresholdHC.CriticalEntropy.CriticalCommonPair
import ThresholdHC.CriticalEntropy.CriticalCreation
import ThresholdHC.CriticalEntropy.CriticalExperiment
import ThresholdHC.CriticalEntropy.CriticalGeometry
import ThresholdHC.CriticalEntropy.CriticalLaw
import ThresholdHC.CriticalEntropy.CriticalMinimax
import ThresholdHC.CriticalEntropy.CriticalModel
import ThresholdHC.CriticalEntropy.CriticalPopulationFinite
import ThresholdHC.CriticalEntropy.CriticalRareModel
import ThresholdHC.CriticalEntropy.CriticalRate
import ThresholdHC.CriticalEntropy.CriticalRisk
import ThresholdHC.CriticalEntropy.CriticalScale
import ThresholdHC.CriticalEntropy.CriticalTerminalAffinity
import ThresholdHC.CriticalEntropy.CriticalTermination
import ThresholdHC.CriticalEntropy.EarlyDecision
import ThresholdHC.CriticalEntropy.EstimationEntropy
import ThresholdHC.CriticalEntropy.EventInformation
import ThresholdHC.CriticalEntropy.EventualAffinity
import ThresholdHC.CriticalEntropy.ExponentialRisk
import ThresholdHC.CriticalEntropy.FiniteAffinity
import ThresholdHC.CriticalEntropy.FiniteCentering
import ThresholdHC.CriticalEntropy.FiniteGap
import ThresholdHC.CriticalEntropy.FiniteGeometry
import ThresholdHC.CriticalEntropy.FiniteGeometryModel
import ThresholdHC.CriticalEntropy.FiniteObservation
import ThresholdHC.CriticalEntropy.FinitePopulation
import ThresholdHC.CriticalEntropy.FiniteRMS
import ThresholdHC.CriticalEntropy.FiniteRiskAnalytic
import ThresholdHC.CriticalEntropy.FiniteRiskModel
import ThresholdHC.CriticalEntropy.FiniteSaddle
import ThresholdHC.CriticalEntropy.FiniteSufficiency
import ThresholdHC.CriticalEntropy.FiniteSupport
import ThresholdHC.CriticalEntropy.GapSelection
import ThresholdHC.CriticalEntropy.GeometricOverlap
import ThresholdHC.CriticalEntropy.GoodGapModel
import ThresholdHC.CriticalEntropy.GoodGaps
import ThresholdHC.CriticalEntropy.HalfPrior
import ThresholdHC.CriticalEntropy.Hellinger
import ThresholdHC.CriticalEntropy.HellingerGeometry
import ThresholdHC.CriticalEntropy.HellingerModel
import ThresholdHC.CriticalEntropy.LikelihoodAffine
import ThresholdHC.CriticalEntropy.LikelihoodBounds
import ThresholdHC.CriticalEntropy.LocalSimulation
import ThresholdHC.CriticalEntropy.MidpointWork
import ThresholdHC.CriticalEntropy.ObservablePopulation
import ThresholdHC.CriticalEntropy.ObservationAffine
import ThresholdHC.CriticalEntropy.ObservationGeometryModel
import ThresholdHC.CriticalEntropy.ObservationInformation
import ThresholdHC.CriticalEntropy.ObservationModel
import ThresholdHC.CriticalEntropy.ObservationRisk
import ThresholdHC.CriticalEntropy.Packing
import ThresholdHC.CriticalEntropy.PolicyMixture
import ThresholdHC.CriticalEntropy.PolicyNormalization
import ThresholdHC.CriticalEntropy.PopulationCompactness
import ThresholdHC.CriticalEntropy.PopulationGeometryModel
import ThresholdHC.CriticalEntropy.PopulationLocalWork
import ThresholdHC.CriticalEntropy.PopulationMixture
import ThresholdHC.CriticalEntropy.PopulationModel
import ThresholdHC.CriticalEntropy.PopulationTapeLaw
import ThresholdHC.CriticalEntropy.PopulationTransfer
import ThresholdHC.CriticalEntropy.PopulationVariance
import ThresholdHC.CriticalEntropy.PopulationWorkLaw
import ThresholdHC.CriticalEntropy.RepeatedModel
import ThresholdHC.CriticalEntropy.RepeatedRestart
import ThresholdHC.CriticalEntropy.RepeatedSignModel
import ThresholdHC.CriticalEntropy.RestartPair
import ThresholdHC.CriticalEntropy.SampleMean
import ThresholdHC.CriticalEntropy.ScaleAsymptotics
import ThresholdHC.CriticalEntropy.SeedAdaptation
import ThresholdHC.CriticalEntropy.SeedAffinity
import ThresholdHC.CriticalEntropy.SeededPopulationTransfer
import ThresholdHC.CriticalEntropy.SelectedPolicy
import ThresholdHC.CriticalEntropy.SequentialModel
import ThresholdHC.CriticalEntropy.SignReduction
import ThresholdHC.CriticalEntropy.SignTest
import ThresholdHC.CriticalEntropy.StatisticProcedure
import ThresholdHC.CriticalEntropy.StoppedModel
import ThresholdHC.CriticalEntropy.StoppedTape
import ThresholdHC.CriticalEntropy.StoppingWindow
import ThresholdHC.CriticalEntropy.SymmetricReduction
import ThresholdHC.CriticalEntropy.UniformCoin
import ThresholdHC.CriticalUpper.Average
import ThresholdHC.CriticalUpper.Budget
import ThresholdHC.CriticalUpper.Calibration
import ThresholdHC.CriticalUpper.CappedCost
import ThresholdHC.CriticalUpper.CoinLaw
import ThresholdHC.CriticalUpper.CoupledModel
import ThresholdHC.CriticalUpper.FixedBounds
import ThresholdHC.CriticalUpper.FixedExecution
import ThresholdHC.CriticalUpper.FixedIdentities
import ThresholdHC.CriticalUpper.FixedModel
import ThresholdHC.CriticalUpper.Full
import ThresholdHC.CriticalUpper.GapIntegration
import ThresholdHC.CriticalUpper.Increment
import ThresholdHC.CriticalUpper.Parameters
import ThresholdHC.CriticalUpper.ScreenCoin
import ThresholdHC.CriticalUpper.ScreenError
import ThresholdHC.CriticalUpper.ScreenModel
import ThresholdHC.CriticalUpper.ScreenMoments
import ThresholdHC.CriticalUpper.ScreenPopulation
import ThresholdHC.CriticalUpper.ScreenWork
import ThresholdHC.CriticalUpper.Simulation
import ThresholdHC.CriticalUpper.Specification
import ThresholdHC.CriticalUpper.Unbiased
import ThresholdHC.CriticalUpper.UnbiasedPopulation
import ThresholdHC.CriticalUpper.UnbiasedWork
import ThresholdHC.CriticalUpper.WeightedCost
import ThresholdHC.EntropyTail.Band
import ThresholdHC.EntropyTail.Bridge
import ThresholdHC.EntropyTail.Entropy
import ThresholdHC.EntropyTail.Gamma
import ThresholdHC.EntropyTail.HardSelection
import ThresholdHC.EntropyTail.Model
import ThresholdHC.EntropyTail.Objective
import ThresholdHC.EntropyTail.Specification
import ThresholdHC.EntropyTail.Superadditive
import ThresholdHC.EntropyTail.Upper
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
import ThresholdHC.EntropyTailLower.ActivationGate
import ThresholdHC.EntropyTailLower.AnnularEstimation
import ThresholdHC.EntropyTailLower.AnnularWork
import ThresholdHC.EntropyTailLower.CanonicalBands
import ThresholdHC.EntropyTailLower.CanonicalGroups
import ThresholdHC.EntropyTailLower.CertificateAnnular
import ThresholdHC.EntropyTailLower.CertificateCentering
import ThresholdHC.EntropyTailLower.CertificateLabel
import ThresholdHC.EntropyTailLower.CertificateOneCoin
import ThresholdHC.EntropyTailLower.ComparableGroups
import ThresholdHC.EntropyTailLower.ComponentLocalization
import ThresholdHC.EntropyTailLower.ComponentPriors
import ThresholdHC.EntropyTailLower.DyadicMass
import ThresholdHC.EntropyTailLower.EarlyLikelihood
import ThresholdHC.EntropyTailLower.EarlyMean
import ThresholdHC.EntropyTailLower.EarlyOutput
import ThresholdHC.EntropyTailLower.EntropyIncrement
import ThresholdHC.EntropyTailLower.EntropyPacking
import ThresholdHC.EntropyTailLower.EntropyTiers
import ThresholdHC.EntropyTailLower.FairGateWork
import ThresholdHC.EntropyTailLower.FiniteAllocation
import ThresholdHC.EntropyTailLower.FiniteAverageProcedure
import ThresholdHC.EntropyTailLower.FiniteBandApprox
import ThresholdHC.EntropyTailLower.FiniteSelection
import ThresholdHC.EntropyTailLower.FlowOneCoin
import ThresholdHC.EntropyTailLower.FractionalPrior
import ThresholdHC.EntropyTailLower.GateAverage
import ThresholdHC.EntropyTailLower.GateLikelihood
import ThresholdHC.EntropyTailLower.GateMeasure
import ThresholdHC.EntropyTailLower.GateMomentFloor
import ThresholdHC.EntropyTailLower.GatedAnnular
import ThresholdHC.EntropyTailLower.GatedGoodGaps
import ThresholdHC.EntropyTailLower.GatedOutput
import ThresholdHC.EntropyTailLower.GeneralGoodGaps
import ThresholdHC.EntropyTailLower.GlobalCosts
import ThresholdHC.EntropyTailLower.JointAllocation
import ThresholdHC.EntropyTailLower.LabelAllocation
import ThresholdHC.EntropyTailLower.LargeGapEntropy
import ThresholdHC.EntropyTailLower.LocalizationAlgebra
import ThresholdHC.EntropyTailLower.LocalizedAnnular
import ThresholdHC.EntropyTailLower.OptimalRetained
import ThresholdHC.EntropyTailLower.PackedAllocation
import ThresholdHC.EntropyTailLower.PopulationAnnular
import ThresholdHC.EntropyTailLower.PopulationGateAverage
import ThresholdHC.EntropyTailLower.PopulationPullback
import ThresholdHC.EntropyTailLower.RetainedFamily
import ThresholdHC.EntropyTailLower.RetainedGap
import ThresholdHC.EntropyTailLower.SeparatedGroups
import ThresholdHC.EntropyTailLower.Specification
import ThresholdHC.EntropyTailLower.TrimmedGroup
import ThresholdHC.EntropyTailLower.WeightedEstimation
import ThresholdHC.EntropyTailLower.WeightedOverlap
import ThresholdHC.EntropyTailLower.WeightedSign
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
import ThresholdHC.EntropyTailSharp.Annular
import ThresholdHC.EntropyTailSharp.Certificate
import ThresholdHC.EntropyTailSharp.Core
import ThresholdHC.EntropyTailSharp.CoreRisk
import ThresholdHC.EntropyTailSharp.Full
import ThresholdHC.EntropyTailSharp.Groups
import ThresholdHC.EntropyTailSharp.Specification
import ThresholdHC.EntropyTailSharp.TailInformation
import ThresholdHC.EntropyTailSharp.TailRisk
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
import ThresholdHC.FiniteQuantile.Allocation
import ThresholdHC.FiniteQuantile.Core
import ThresholdHC.FiniteQuantile.CoreRisk
import ThresholdHC.FiniteQuantile.CoreValue
import ThresholdHC.FiniteQuantile.Filter
import ThresholdHC.FiniteQuantile.FilteredPacking
import ThresholdHC.FiniteQuantile.FiniteInformation
import ThresholdHC.FiniteQuantile.PosteriorEnergy
import ThresholdHC.FiniteQuantile.TailInformation
import ThresholdHC.FiniteQuantile.TailPair
import ThresholdHC.FiniteQuantile.TailRisk
import ThresholdHC.Genie.CapLimits
import ThresholdHC.Genie.CapMonotonicity
import ThresholdHC.Genie.CompactDecreasingMaximum
import ThresholdHC.Genie.CompactPriorDomain
import ThresholdHC.Genie.DualTopology
import ThresholdHC.Genie.ExtendedFlowConservation
import ThresholdHC.Genie.FlowExtension
import ThresholdHC.Genie.FlowTruncation
import ThresholdHC.Genie.InfiniteComparison
import ThresholdHC.Genie.InfiniteCoordinates
import ThresholdHC.Genie.InfiniteDualLimit
import ThresholdHC.Genie.InfiniteDuality
import ThresholdHC.Genie.InformationTopology
import ThresholdHC.Genie.Model
import ThresholdHC.Genie.OptimizedBrackets
import ThresholdHC.Genie.PerspectiveIntegral
import ThresholdHC.Genie.PerspectiveTopology
import ThresholdHC.Genie.ReferenceRegularization
import ThresholdHC.Genie.RevealProgram
import ThresholdHC.Genie.RevealReward
import ThresholdHC.Genie.RevealTruncation
import ThresholdHC.HardBudget.Application
import ThresholdHC.HardBudget.BudgetScale
import ThresholdHC.HardBudget.Controller
import ThresholdHC.HardBudget.Critical
import ThresholdHC.HardBudget.CriticalTransport
import ThresholdHC.HardBudget.Execution
import ThresholdHC.HardBudget.Full
import ThresholdHC.HardBudget.Inputs
import ThresholdHC.HardBudget.Rare
import ThresholdHC.HardBudget.RareModel
import ThresholdHC.HardBudget.Rate
import ThresholdHC.HardBudget.Recurrence
import ThresholdHC.HardBudget.Schedule
import ThresholdHC.HardBudget.SelectionScale
import ThresholdHC.HardBudget.Specification
import ThresholdHC.HardBudget.Stage
import ThresholdHC.HardBudget.StageMoments
import ThresholdHC.HardBudget.Words
import ThresholdHC.KnownLawPlanner.PlanAllocation
import ThresholdHC.KnownLawPlanner.PlanCaps
import ThresholdHC.KnownLawPlanner.PlanCertificate
import ThresholdHC.KnownLawPlanner.PlanFamily
import ThresholdHC.KnownLawPlanner.PlanQuantileRate
import ThresholdHC.KnownLawPlanner.PlanRate
import ThresholdHC.KnownLawPlanner.PlanTightQuantileRate
import ThresholdHC.KnownLawPlanner.PlanTightRate
import ThresholdHC.KnownLawPlanner.PlanZeroAtomRate
import ThresholdHC.KnownLawPlanner.PlannedEstimator
import ThresholdHC.KnownLawPlanner.PlannerOutput
import ThresholdHC.LawAdaptation.Concentration
import ThresholdHC.LawAdaptation.Controller
import ThresholdHC.LawAdaptation.Execution
import ThresholdHC.LawAdaptation.Identification
import ThresholdHC.LawAdaptation.Moments
import ThresholdHC.LawAdaptation.Observation
import ThresholdHC.LawAdaptation.Parity
import ThresholdHC.LawAdaptation.Pilot
import ThresholdHC.ObservableSimulation.LawUniqueness
import ThresholdHC.ObservableSimulation.OriginalExperiment
import ThresholdHC.ObservableSimulation.PopulationLaw
import ThresholdHC.ObservableSimulation.PopulationPath
import ThresholdHC.ObservableSimulation.SimulationCap
import ThresholdHC.Proofs.Algebra
import ThresholdHC.Proofs.Calibration
import ThresholdHC.Proofs.Classifier
import ThresholdHC.Proofs.Constants
import ThresholdHC.Proofs.Hellinger
import ThresholdHC.Proofs.KL
import ThresholdHC.Proofs.Tier2.ClassifierBridge
import ThresholdHC.Proofs.Tier2.ClassifierExpectations
import ThresholdHC.Proofs.Tier2.ClassifierModel
import ThresholdHC.Proofs.Tier2.ClassifierMoments
import ThresholdHC.Proofs.Tier2.ClassifierPrefix
import ThresholdHC.Proofs.Tier2.ClassifierProb
import ThresholdHC.Proofs.Tier2.ClassifierProbability
import ThresholdHC.Proofs.Tier2.ClassifierTelescoping
import ThresholdHC.Proofs.Tier2.Information
import ThresholdHC.Proofs.Tier2.InformationCore
import ThresholdHC.Proofs.Tier2.Transcript
import ThresholdHC.Proofs.Tier2.TranscriptBase
import ThresholdHC.Proofs.Tier2.TranscriptLikelihood
import ThresholdHC.Proofs.Tier2.TranscriptScalar
import ThresholdHC.QuantileComparison.Scalar
import ThresholdHC.QuantileComparison.Specification
import ThresholdHC.QuantileSelection.BinaryEntropy
import ThresholdHC.QuantileSelection.Full
import ThresholdHC.QuantileSelection.Interaction
import ThresholdHC.QuantileSelection.MeasureEntropy
import ThresholdHC.QuantileSelection.Pointwise
import ThresholdHC.QuantileSelection.Price
import ThresholdHC.QuantileSelection.ScaleWeights
import ThresholdHC.QuantileSelection.SeparatedCost
import ThresholdHC.QuantileSelection.Specification
import ThresholdHC.RareAboveTwo.BandError
import ThresholdHC.RareAboveTwo.BandModel
import ThresholdHC.RareAboveTwo.Bias
import ThresholdHC.RareAboveTwo.BudgetMath
import ThresholdHC.RareAboveTwo.CoupledModel
import ThresholdHC.RareAboveTwo.Increment
import ThresholdHC.RareAboveTwo.Margin
import ThresholdHC.RareAboveTwo.Model
import ThresholdHC.RareAboveTwo.Nonvacuity
import ThresholdHC.RareAboveTwo.Parameters
import ThresholdHC.RareAboveTwo.PopulationError
import ThresholdHC.RareAboveTwo.Specification
import ThresholdHC.RareAboveTwo.Terminal
import ThresholdHC.RareAboveTwo.TerminalInformation
import ThresholdHC.RobustContinuation.CDFBridge
import ThresholdHC.RobustContinuation.CappedMedian
import ThresholdHC.RobustContinuation.ClassifierOrder
import ThresholdHC.RobustContinuation.Clipping
import ThresholdHC.RobustContinuation.CouplingSplit
import ThresholdHC.RobustContinuation.PaidCoverage
import ThresholdHC.RobustContinuation.PaidMedian
import ThresholdHC.RobustContinuation.PilotIndependence
import ThresholdHC.RobustContinuation.RaceOrder
import ThresholdHC.RobustContinuation.ReferenceBase
import ThresholdHC.RobustContinuation.RobustCoinWork
import ThresholdHC.RobustContinuation.RobustLevelCertificates
import ThresholdHC.RobustContinuation.RobustLevelError
import ThresholdHC.RobustContinuation.RobustPlan
import ThresholdHC.RobustContinuation.RobustPlannerOutput
import ThresholdHC.RobustContinuation.TapeOrder
import ThresholdHC.Statements
import ThresholdHC.Statements2
import ThresholdHC.StoppingProgram.AbsorbedPriors
import ThresholdHC.StoppingProgram.AbsorptionRatio
import ThresholdHC.StoppingProgram.AffinityOverlap
import ThresholdHC.StoppingProgram.AffinityRisk
import ThresholdHC.StoppingProgram.Bellman
import ThresholdHC.StoppingProgram.BellmanFlow
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
import ThresholdHC.Tier3.Examples
import ThresholdHC.Tier3.ExamplesModel
import ThresholdHC.Tier3.IntegralLogSum
import ThresholdHC.Tier3.OptimizerModel
import ThresholdHC.Tier3.Randomized
import ThresholdHC.Tier3.RandomizedBase
import ThresholdHC.Tier3.RandomizedModel
import ThresholdHC.Tier3.Stopping
import ThresholdHC.Tier3.StoppingBase
import ThresholdHC.Tier3.StoppingModel
import ThresholdHC.Tier3.TranscriptRatio
import ThresholdHC.Tier4.BoundReduction
import ThresholdHC.Tier4.Entropy
import ThresholdHC.Tier4.FiniteDensity
import ThresholdHC.Tier4.Model
import ThresholdHC.Tier4.StoppedReconstruction
import ThresholdHC.Tier5.BoundReduction
import ThresholdHC.Tier5.CreationBase
import ThresholdHC.Tier5.CreationExample
import ThresholdHC.Tier5.CreationFresh
import ThresholdHC.Tier5.CreationModel
import ThresholdHC.Tier5.CreationPadding
import ThresholdHC.Tier5.CreationProduct
import ThresholdHC.Tier5.Entropy
import ThresholdHC.Tier5.EntropyPrefix
import ThresholdHC.Tier5.FiniteCreation
import ThresholdHC.Tier5.FiniteEnvironment
import ThresholdHC.Tier5.FiniteJoint
import ThresholdHC.Tier5.Full
import ThresholdHC.Tier5.Model
import ThresholdHC.Tier5.PriorRatio
import ThresholdHC.Tier5.Specification
import ThresholdHC.Tier5.StoppingBase
import ThresholdHC.Tier5.StoppingEntropy
import ThresholdHC.Tier5.StoppingFull
import ThresholdHC.Tier6.AlgorithmCore
import ThresholdHC.Tier6.AlgorithmModel
import ThresholdHC.Tier6.AlgorithmNonempty
import ThresholdHC.Tier6.AlgorithmRisk
import ThresholdHC.Tier6.Full
import ThresholdHC.Tier6.HardPair
import ThresholdHC.Tier6.HardPairModel
import ThresholdHC.Tier6.ModelReduction
import ThresholdHC.Tier6.Process
import ThresholdHC.Tier6.ProcessIntegral
import ThresholdHC.Tier6.ProcessModel
import ThresholdHC.Tier6.ProcessWeights
import ThresholdHC.Tier6.RiskReduction
import ThresholdHC.Tier6.Specification
import ThresholdHC.Tier6.Testing
import ThresholdHC.Tier6.TestingFinite
import ThresholdHC.Tier6.TestingModel
import ThresholdHC.UnbiasedConverse.TwoPoint
import ThresholdHC.Uniform713.Arithmetic
import ThresholdHC.Uniform713.Classifier
import ThresholdHC.Uniform713.ClassifierModel
import ThresholdHC.Uniform713.Common
import ThresholdHC.Uniform713.Concentration
import ThresholdHC.Uniform713.Estimator
import ThresholdHC.Uniform713.Series
import ThresholdHC.Uniform713.WorkArithmetic

open Lean Elab Command in
elab "#project_axioms" : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let allowed : NameSet :=
    ({} : NameSet).insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound
  let mut constants : Nat := 0
  let mut theorems : Nat := 0
  let mut declared : Array Name := #[]
  let mut offenders : Array Name := #[]
  let mut used : NameSet := {}
  for (c, info) in env.constants.map₁.toList do
    match env.getModuleIdxFor? c with
    | some idx =>
      if (`ThresholdHC).isPrefixOf mods[idx.toNat]! then
        constants := constants + 1
        match info with
        | .thmInfo _ => theorems := theorems + 1
        | .axiomInfo _ => declared := declared.push c
        | _ => pure ()
        let axioms ← collectAxioms c
        for a in axioms do
          used := used.insert a
        if axioms.any (fun a => !allowed.contains a) then offenders := offenders.push c
    | none => pure ()
  let project := (mods.filter fun m => (`ThresholdHC).isPrefixOf m).size
  logInfo m!"PROJECT_AXIOMS modules={project}"
  logInfo m!"PROJECT_AXIOMS constants={constants}"
  logInfo m!"PROJECT_AXIOMS theorems={theorems}"
  logInfo m!"PROJECT_AXIOMS declared={declared.qsort Name.lt}"
  logInfo m!"PROJECT_AXIOMS used={used.toArray.qsort Name.lt}"
  logInfo m!"PROJECT_AXIOMS offenders={offenders.qsort Name.lt}"

open Lean Elab Command Meta in
elab "#project_definitions" : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let project (c : Name) : Bool := match env.getModuleIdxFor? c with
    | some idx => (`ThresholdHC).isPrefixOf mods[idx.toNat]!
    | none => false
  -- Every instance a project module exports, scoped instances included.
  for i in [0:mods.size] do
    if (`ThresholdHC).isPrefixOf mods[i]! then
      for entry in instanceExtension.ext.getModuleEntries env (show ModuleIdx from i) do
        let (scope, e) := match entry with
          | .global e => ("global", e)
          | .scoped ns e => (s!"scoped:{ns}", e)
        let kind ← liftTermElabM do
          let ty ← inferType e.val
          if ← isProp ty then
            return "prop"
          let body ← forallTelescopeReducing ty fun _ b => pure b
          return if body.getUsedConstants.any project then "data" else "orphan"
        logInfo m!"PROJECT_INSTANCE {e.globalName?.getD .anonymous} {scope} {e.priority} {kind}"
  -- A fingerprint of every definition and inductive type, with proofs erased,
  -- and of the matchers and auxiliary definitions they use. Matchers and the
  -- auxiliary definitions of a theorem's proof are not roots, so a proof can
  -- change without changing the lock.
  let erase (e : Expr) : MetaM Expr :=
    Meta.transform e (pre := fun s => do
      if ← isProof s then return .done (.const ``True.intro []) else return .continue)
  let ofTheorem (c : Name) : Bool := Id.run do
    let mut p := c.getPrefix
    while !p.isAnonymous do
      if let some (.thmInfo _) := env.find? p then
        return true
      p := p.getPrefix
    return false
  let mut pending : Array Name := #[]
  for (c, info) in env.constants.map₁.toList do
    if project c && !ofTheorem c then
      match info with
      | .defnInfo _ => if !isMatcherCore env c then pending := pending.push c
      | .inductInfo _ => pending := pending.push c
      | _ => pure ()
  let mut seen : NameSet := {}
  let mut out : Array (Name × String) := #[]
  while !pending.isEmpty do
    let c := pending.back!
    pending := pending.pop
    if seen.contains c then continue
    seen := seen.insert c
    let mut parts : Array Expr := #[]
    match env.find? c with
    | some (.defnInfo d) =>
      parts := #[← liftTermElabM (erase d.type), ← liftTermElabM (erase d.value)]
    | some (.inductInfo d) =>
      parts := #[← liftTermElabM (erase d.type)]
      for ctor in d.ctors do
        if let some ci := env.find? ctor then
          parts := parts.push (← liftTermElabM (erase ci.type))
    | _ => continue
    out := out.push (c, ":".intercalate (parts.toList.map fun p => toString (toString p).hash))
    for p in parts do
      for n in p.getUsedConstants do
        if project n && !seen.contains n then pending := pending.push n
  logInfo m!"PROJECT_DEFINITIONS count={out.size}"
  for (c, f) in out.qsort (fun a b => a.1.lt b.1) do
    logInfo m!"PROJECT_DEFINITION {c} {f}"

#project_axioms
#project_definitions
