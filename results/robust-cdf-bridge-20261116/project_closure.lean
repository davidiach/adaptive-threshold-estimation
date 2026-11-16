import ThresholdHC.ArbitraryLawAdaptation.BandGeometry
import ThresholdHC.ArbitraryLawAdaptation.BandPenalty
import ThresholdHC.ArbitraryLawAdaptation.CDFCoupling
import ThresholdHC.ArbitraryLawAdaptation.CDFSelection
import ThresholdHC.ArbitraryLawAdaptation.CountableEntropy
import ThresholdHC.ArbitraryLawAdaptation.CountableTransport
import ThresholdHC.ArbitraryLawAdaptation.CouplingEntropy
import ThresholdHC.ArbitraryLawAdaptation.DominatedMass
import ThresholdHC.ArbitraryLawAdaptation.DominatedSelection
import ThresholdHC.ArbitraryLawAdaptation.EntropyTransport
import ThresholdHC.ArbitraryLawAdaptation.GammaTransport
import ThresholdHC.ArbitraryLawAdaptation.IncreasingSelection
import ThresholdHC.ArbitraryLawAdaptation.SelectionLift
import ThresholdHC.ArbitraryLawAdaptation.TransportCells
import ThresholdHC.ArbitraryLawAdaptation.ZeroAlgebra
import ThresholdHC.ArbitraryLawAdaptation.ZeroCoupling
import ThresholdHC.ArbitraryLawAdaptation.ZeroModel
import ThresholdHC.ArbitraryLawAdaptation.ZeroQuantile
import ThresholdHC.ArbitraryLawAdaptation.ZeroSelection
import ThresholdHC.BlindUpper.ActualBatch
import ThresholdHC.BlindUpper.BatchMachine
import ThresholdHC.BlindUpper.BatchPath
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
import ThresholdHC.BlindUpper.TerminalOutput
import ThresholdHC.CriticalEntropy.Activation
import ThresholdHC.CriticalEntropy.ActivationCost
import ThresholdHC.CriticalEntropy.ActivationModel
import ThresholdHC.CriticalEntropy.BaseCost
import ThresholdHC.CriticalEntropy.BernoulliPrefix
import ThresholdHC.CriticalEntropy.CapInvariance
import ThresholdHC.CriticalEntropy.CappedObservation
import ThresholdHC.CriticalEntropy.CommonPoint
import ThresholdHC.CriticalEntropy.ConditionalMoments
import ThresholdHC.CriticalEntropy.CreationPopulation
import ThresholdHC.CriticalEntropy.CriticalAnnuli
import ThresholdHC.CriticalEntropy.CriticalCommonPair
import ThresholdHC.CriticalEntropy.CriticalGeometry
import ThresholdHC.CriticalEntropy.CriticalLaw
import ThresholdHC.CriticalEntropy.CriticalModel
import ThresholdHC.CriticalEntropy.CriticalRisk
import ThresholdHC.CriticalEntropy.CriticalScale
import ThresholdHC.CriticalEntropy.EarlyDecision
import ThresholdHC.CriticalEntropy.EstimationEntropy
import ThresholdHC.CriticalEntropy.EventInformation
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
import ThresholdHC.CriticalEntropy.PopulationVariance
import ThresholdHC.CriticalEntropy.RepeatedModel
import ThresholdHC.CriticalEntropy.RepeatedRestart
import ThresholdHC.CriticalEntropy.RepeatedSignModel
import ThresholdHC.CriticalEntropy.RestartPair
import ThresholdHC.CriticalEntropy.SampleMean
import ThresholdHC.CriticalEntropy.ScaleAsymptotics
import ThresholdHC.CriticalEntropy.SeedAdaptation
import ThresholdHC.CriticalEntropy.SeedAffinity
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
import ThresholdHC.CriticalUpper.Calibration
import ThresholdHC.CriticalUpper.CappedCost
import ThresholdHC.CriticalUpper.CoinLaw
import ThresholdHC.CriticalUpper.CoupledModel
import ThresholdHC.CriticalUpper.GapIntegration
import ThresholdHC.CriticalUpper.Increment
import ThresholdHC.CriticalUpper.Parameters
import ThresholdHC.CriticalUpper.ScreenCoin
import ThresholdHC.CriticalUpper.ScreenError
import ThresholdHC.CriticalUpper.ScreenModel
import ThresholdHC.CriticalUpper.ScreenMoments
import ThresholdHC.CriticalUpper.ScreenPopulation
import ThresholdHC.CriticalUpper.ScreenWork
import ThresholdHC.CriticalUpper.Unbiased
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
import ThresholdHC.EntropyTailExecution.FiniteRisk
import ThresholdHC.EntropyTailExecution.IncrementBounds
import ThresholdHC.EntropyTailExecution.PlanExecution
import ThresholdHC.EntropyTailExecution.PoissonPlan
import ThresholdHC.EntropyTailExecution.RealizedPoisson
import ThresholdHC.EntropyTailExecution.ScheduledFamily
import ThresholdHC.EntropyTailExecution.ThreePiece
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
import ThresholdHC.ObservableSimulation.LawUniqueness
import ThresholdHC.ObservableSimulation.OriginalExperiment
import ThresholdHC.ObservableSimulation.PopulationLaw
import ThresholdHC.ObservableSimulation.PopulationPath
import ThresholdHC.ObservableSimulation.SimulationCap
import ThresholdHC.Proofs.Algebra
import ThresholdHC.Proofs.Calibration
import ThresholdHC.Proofs.Classifier
import ThresholdHC.Proofs.Constants
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
import ThresholdHC.RobustContinuation.CDFBridge
import ThresholdHC.RobustContinuation.ClassifierOrder
import ThresholdHC.RobustContinuation.CouplingSplit
import ThresholdHC.RobustContinuation.RaceOrder
import ThresholdHC.RobustContinuation.RobustCoinWork
import ThresholdHC.RobustContinuation.RobustLevelCertificates
import ThresholdHC.RobustContinuation.RobustLevelError
import ThresholdHC.RobustContinuation.RobustPlan
import ThresholdHC.RobustContinuation.RobustPlannerOutput
import ThresholdHC.RobustContinuation.TapeOrder
import ThresholdHC.Statements
import ThresholdHC.Statements2
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
