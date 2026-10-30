# Entropy–tail and quantile formalization

Work started from `8fc36ac` on branch
`feat/entropy-tail-upper-quantile-20261030`.

The owner assigned this task the remaining formalization except for the
entropy–tail statistical lower bound, which is being developed separately in
an Opus cloud session. The branch and interface of that session are not yet
available. New modules here are additive; existing frozen sources and audits
remain unchanged.

## Scope and completion criteria

1. Prove the homogeneous cost-entropy library and the deterministic comparison
   between the actual entropy–tail selection functional and the actual quantile
   split, including atoms and arbitrary probability laws on positive gaps.
2. Realize the entropy–tail upper construction in the existing observable
   experiment. Prove likelihood-bank error/work bounds, the capped race,
   multilevel allocation, uniform expected work, and actual output risk.
3. Prove the finite-approximation and measure-limit steps and connect the
   resulting upper bound to the unchanged rare-event minimax risk.
4. Integrate the separately proved lower theorem when it is available. Derive
   the general-law closed quantile characterization. Do not replace the missing
   lower theorem by an axiom or count a conditional result as completion.
5. Address the remaining stopping-program, identification, and auxiliary
   paper-only claims as separate developments, with exact statement and
   transitive-axiom audits for each completed result.

The construction proves a bound with coefficient `28000`, and separately
derives both the frozen general-law upper coefficient `33000` and the finite-law
upper coefficient `30001` (also for arbitrary laws). The full dependency and
axiom audit passed: 306 rebuilt local modules, 611 audited declarations, and six
exact types. See the [published record](../results/entropy-tail-upper-20261030/README.md).

## Modules and current boundary

- `ThresholdHC/EntropyTail/CostEntropy.lean`: finite homogeneous entropy,
  normalization, monotonicity, superadditivity, mixture and reference bounds.
- `ThresholdHC/EntropyTail/QuantileAlgebra.lean`: scalar inequality yielding
  `1 + 2 sqrt 2`, separate from the integral and entropy premises.
- `QuantileSplitFull.lean`: the full frozen quantile split, including the
  fractional boundary atom, exact mass, support and finite core entropy.
- `ScaleSeparated.lean`: the measure bound `Gamma <= 4 H/t` with the paper's
  constant, using geometric reference probabilities.
- `EntropyMoment.lean`: extended-real inverse-moment and Cauchy--Schwarz
  bounds, without an inverse-moment assumption.
- `QuantileComparison.lean`: the full frozen arbitrary-law comparison
  `K <= Q <= (1 + 2 sqrt 2) K`. `QuantileTailBound.lean` also proves the
  saturation identity when the budget scale is at least the threshold.
- `ThresholdHC/EntropyTailUpper/Ordinary.lean`: actual single-coin ordinary
  classifier certificates, reusing the existing observable procedure.
- `ThresholdHC/EntropyTailUpper/Allocation.lean`: exact allocation means,
  expected-work and second-moment identities, and certificate optimality.
- `PrefixCrossing.lean`, `BernoulliTilt.lean`, `BankErrors.lean`: countable-time
  reference-bank errors, with the positive test using the full null mixture.
- `BoundedSearch.lean`, `ParityRace.lean`, `BankRace.lean`: an actual finite,
  prefix-observable alternating race; cap, output, error-event and work bounds.
- `PredictableWald.lean`, `ScoreHitting.lean`, `ReferenceDrift.lean`: bounded
  Wald identity and the matching negative-reference work constant.
- `PrefixConcentration.lean`, `ReferenceLikelihood.lean`, `NullPrefix.lean`,
  `NullMixture.lean`, `PositiveRaceWork.lean`, `LaplaceEnvelope.lean`,
  `BankWork.lean`: positive-sign work from the actual full-null prefix law,
  including endpoint gaps. The three-piece envelope requires the selected
  component's inverse-square moment and the resolved tail's inverse moment.
- `PopulationErrors.lean`: the raced error bound
  `rho*epsilon + u + eta_mu(M)` under every globally rare measurable prior.
- `PoissonMoments.lean`: exact first and second moments of actual Poisson
  counts, used by the marked construction described below.
- `SurvivalWork.lean`, `LogSurcharge.lean`: geometric survival-work and scalar
  logarithmic surcharge estimates used in the remaining assembly.
- `ThresholdHC/EntropyTailAssembly/BandWeights.lean`, `BandEntropy.lean`,
  `IntegratedSurcharge.lean`, `SelectedWork.lean`: normalized selected-band
  weights, zero-mass bands, exact entropy sums and integrated selected work.
- `OrdinaryKernels.lean`, `ErrorCaps.lean`, `AccuracySchedule.lean`: ordinary
  error convergence for arbitrary finite laws, least successful caps, strictly
  increasing caps, geometric accuracy and finite terminal levels.
- `KernelMoments.lean`, `DyadicKernelPointwise.lean`, `DyadicKernelSum.lean`:
  component moment estimates and the homogeneous kernel bound with constant
  208, including bounded truncations and infinite extended-value sums.
- `ConditionalWork.lean`, `LevelCertificates.lean`: actual raced population
  error and three-piece work, including zero selected mass. The work estimate
  uses the original globally rare prior and observes no component labels.
- `MixedWork.lean`, `UnresolvedWork.lean`, `CertificateAlgebra.lean`,
  `BudgetCertificate.lean`: a finite multilevel allocation certificate bounded
  by `28000 * (sqrt(rho * Gamma) + H)`, uniformly in the terminal level.
  Intermediate constants are conservative: ordinary inverse-moment work uses
  34 instead of 21, and selected level work uses `128*(l+1)*Gamma + 6*H^2/rho`.
  The sampling and execution modules below now connect this certificate to
  an actual estimator and the minimax risk.
- `FiniteApproximation.lean`: finite entropy implies the selected measure's
  inverse-square and inverse moments are integrable; finite-band truncation
  preserves the entropy upper bound and its discarded inverse moment vanishes.
- `ThresholdHC/EntropyTailSampling/`: genuine marked Poisson laws, their exact
  first and second moments, coupled population moments, and positivity of the
  scheduled stopping costs.
- `ThresholdHC/EntropyTailExecution/CallMachine.lean`, `PlanExecution.lean`,
  `ActualPlan.lean`: an observable controller storing only observed words and
  coin labels, with pointwise execution, output, and charged-work identities.
- `PoissonPlan.lean`, `RealizedPoisson.lean`: distinct population labels realize
  the independent marked Poisson law, including zero counts; exact work and
  squared-risk identities hold in the original population experiment.
- `CoupledCall.lean`, `IncrementBounds.lean`, `AllocatedEstimator.lean`,
  `ScheduledFamily.lean`: adjacent decisions share a coin's prefix, their cost
  is the maximum of the stopping times, and positive Poisson rates realize the
  optimal allocation under the expected-work constraint.
- `FiniteRisk.lean`, `ThreePiece.lean`, `EntropyLimit.lean`: the finite-level
  minimax bound, terminal-level selection, the zero-unresolved-mass limit of
  finite estimators, and removal of the selected-measure support cutoff.
- `UpperTheorem.lean`: the full frozen `EntropyTailUpperStatement` and
  `ClosedQuantileUpperStatement`, plus explicitly typed stronger `28000`
  selection and `30001` quantile upper bounds. No statistical lower theorem
  is imported or assumed.

The full deterministic quantile comparison passed the exact-target and
transitive-axiom audit on 30 October 2026: 20 modules, 121 declarations, two
frozen targets, and a rebuild of all 53 local dependency modules. The evidence
is in `results/entropy-tail-quantile-20261030/`. The observable statistical upper
theorems passed the full audit described below. The stopping-program
results remain unfinished; their separate ingredients are described below.
The statistical lower bound remains assigned to the separate cloud session.
Neither an upper bound nor the deterministic comparison alone establishes
the two-sided minimax characterization.

An additional local checkpoint checked all 22 upper-construction modules and
the transitive axioms of all 188 declarations. Two independent exact-type
checks cover the population error theorem and Poisson second moment. Its
evidence is `.runtime/entropy-tail-upper-checkpoint-20261030/`; it used the
already compiled dependencies, recording all 184 local source hashes, and
did not rebuild that whole dependency closure. It is not the final upper
theorem audit.

The assembly checkpoint in
`.runtime/entropy-tail-assembly-checkpoint-20261030/` rebuilt all 17 assembly
modules and checked four independent exact types and the transitive axioms of
all 338 declarations across the 39 upper/assembly modules. Only
`Classical.choice`, `Quot.sound` and `propext` occur. It recorded the local
dependency sources but used cached objects for dependencies outside the
assembly. At that historical checkpoint the full statistical upper theorem
was unverified. The later sampling/execution construction completes those
proof obligations. The subsequent full audit rebuilt 306 local dependency
modules and passed six exact targets and the transitive-axiom checks for 611
declarations across 77 modules. Its `valid` field is true and only the three
standard axioms occur. The [published evidence](../results/entropy-tail-upper-20261030/README.md)
preserves `.runtime/entropy-tail-full-upper-20261030/` with all 307 command logs.

## Verification

Use the repository's pinned Lean toolchain and Mathlib revision. New results
must have exact target checks, complete transitive axiom reports, source
identity checks and a clean proof-escape scan. Retain the existing experiment,
global rarity constraint, all positive budgets, and extended-real risks.
The proof interface must not assume hidden component labels, an integrable
inverse moment, a finite support law, or a deterministic total sampling cap.

The deterministic audit is `python tools/verify_entropy_tail_components.py`.
It recompiles every local dependency and reports the unproved statistical
targets as unverified. Its regression tests are
`python -m unittest discover -s tools -p test_entropy_tail_components.py -v`.

The analytic assembly audit is `python tools/verify_entropy_tail_assembly.py`.
Its default rebuilds the complete local dependency closure. The explicit
`--cached-dependencies` checkpoint mode rebuilds the assembly and records its
more limited rebuild scope. Both modes keep the unproved statistical targets
marked unverified.

The full upper audit is `python tools/verify_entropy_tail_upper.py`. Its default
rebuilds the entire local dependency closure and checks the frozen targets.
`--cached-dependencies` explicitly records a narrower checkpoint rebuild.
Run its regression checks with
`python -m unittest discover -s tools -p test_entropy_tail_upper.py -v`.
The audit never marks the statistical lower bound, two-sided minimax
characterization, or stopping-program theorems as verified.

## Stopping and identification ingredients

The separate checkpoint `.runtime/stopping-components-checkpoint-20261030/`
rebuilds 10 new modules and checks 108 declarations, four independently stated
types, and all transitive axioms. It uses cached dependency objects and records
their source identities. Only `Classical.choice`, `Quot.sound`, and `propext`
occur. Its scope is deliberately narrower than the full paper statements:

- `StoppingProgram/Bellman.lean` and `PriceRatio.lean`: finite stopping trees,
  deterministic maximizers, work bounds, continuity, strict price monotonicity,
  and a unique zero equal to the maximal information/work ratio. Randomized
  finite mixtures cannot improve the price objective.
- `Perspective.lean`: the closed quadratic perspective, null references,
  subadditivity, scaling, and exact scalar output elimination.
- `Model.lean` and `Specification.lean`: the actual normalized flow cone,
  robust certificate program, four-prior information ratio, and explicit
  unproved full theorem targets. Definitions are not counted as proofs of
  strong duality or statistical realization.
- `FlowBasics.lean` and `FlowBounds.lean`: coefficient positivity, the first
  observation's root charge, a finite constant certificate, intensity bounds,
  and vanishing stopping/continuation/output weights at zero intensity.
- `CapIdentification/Interpolation.lean`, `OddPolynomials.lean`, and
  `FiniteSeparation.lean`: interpolation and the converse root-count bound,
  a separating moment contrast, and the exact algebraic threshold
  `N >= 2*m-1` for determining the target from odd moments on `m` distinct
  positive magnitudes.

At that checkpoint the connection to Bernoulli count laws and the support
claims were still unproved. The later checkpoint
`.runtime/cap-identification-checkpoint-20261030/` rebuilt 23 modules, checked
177 declarations and nine independent exact types, and found only
`Classical.choice`, `Quot.sound`, and `propext` in their transitive axioms.
It also used cached dependency objects and recorded their source identities.
The added results are:

- Exact equivalence between the first `ceil(N/2)` odd moments and all capped
  count coefficients, for arbitrary finite gap laws.
- Equality of the actual seed-and-stopped-word law for every independently
  randomized single-unit procedure with cap `N` under matching priors.
- A proved full-depth flow, and `K_N = 0` exactly when the endpoint priors
  match those odd moments.
- The statistical target-identification threshold `N >= 2*m-1` for a law
  with exactly `m` support points, using actual globally rare sign priors.
- For infinite support, actual rare priors with matching capped laws and a
  strictly positive target gap; consequently the primal program has a positive
  bias floor uniform over all budgets at each fixed cap. The construction uses
  the orthogonal polynomial residual in `L2`, with all boundedness and
  integrability obligations proved.

The later [fixed-cap checkpoint](../results/cap-identification-20261030/README.md)
rebuilt 36 modules and checked 245 declarations and ten exact types. It proves
diameter attainment, compact actual-prior moment images, affine recovery,
explicit full-depth certificates, and the exact infinite-budget limit
`P_N(B) -> Delta_N/2`. The combined theorem is
`CapIdentification/Full.lean:fixed_cap_identification`. Only the three standard
axioms occur. Dependencies outside the two groups used cached objects, with
their source identities recorded. The `full_cap_identification_verified`
field is true for this checkpoint.

The subsequent [attained-duality checkpoint](../results/stopping-dual-20261030/README.md)
proves the unchanged `StoppingProgram/Specification.lean:AttainedDualStatement`.
It establishes the exact four-prior value identity, primal and dual attainment,
positive value, and a finite optimal information ratio. The proof uses the
actual global rarity class, geometric separation, compact minimax, explicit
output elimination, and compact primal sublevels with null coordinates removed.
It checks 188 declarations in 30 modules, both the specification and an
independently expanded exact type, and only the three standard axioms. This
checkpoint rebuilt the six attainment modules and used cached dependency
objects with recorded source identities. Reproduce with
`python tools/verify_stopping_dual.py`; its four regression tests are
`python -m unittest discover -s tools -p test_stopping_dual.py -v`.

The [rarity-support checkpoint](../results/rarity-support-20261030/README.md)
proves the scalar minimum formula and an actual fractional cutoff optimizer
for measurable L2 functions bounded above almost everywhere. The cutoff lies
in the supplied nonnegative upper bound; a positive cutoff saturates rarity.
It includes null cutoff sets and atoms. The audit rebuilt six modules, checked
41 declarations in nine modules and two independently stated types, and found
only the three standard axioms. It used cached dependencies with recorded
source identities. Run `python tools/verify_rarity_support.py`; the four
regression tests are `python -m unittest discover -s tools -p test_rarity_support.py -v`.

The [finite-program checkpoint](../results/finite-stopping-program-20261030/README.md)
proves the four-cutoff reduction for arbitrary laws and the exact finite conic
representation for finitely supported laws. It includes both bias signs,
variance and work, with zero weights and repeated support points allowed.
Its audit rebuilt two new modules, checked 119 declarations in 17 modules and
two exact types, and found only the three standard axioms. Dependencies used
cached objects with recorded identities. Run `python tools/verify_finite_stopping_program.py`;
the four regression tests use `test_finite_stopping_program.py`.

The [flow-mixture checkpoint](../results/stopping-flow-mixture-20261030/README.md)
proves exact finite decision-table weights for every cone flow, total stopping
mass, Bellman upper bounds, and actual bounded observable calls for the tables.
It rebuilt ten modules and audited 158 declarations in 17 modules and five
exact types, with cached dependencies and only the standard axioms. At that
checkpoint, the statistical moments and Poisson realization were still open. Run `python tools/verify_stopping_flow_mixture.py`; its four
regression tests use `test_stopping_flow_mixture.py`.

The [program-upper checkpoint](../results/stopping-program-upper-20261030/README.md)
now proves actual stopped-table moments, Poisson certificate realization, and
the unchanged `ProgramUpperStatement`: `R <= P_N`. It rebuilt fourteen modules,
checked 304 declarations in 45 modules and three exact types, and found only
the standard axioms. Dependencies used cached objects with recorded identities.
Run `python tools/verify_stopping_program_upper.py`; its four regression tests
use `test_stopping_program_upper.py`.

The [reference-absorption checkpoint](../results/reference-absorption-20261030/README.md)
proves `D_N <= P_N <= 3 D_N` for the actual globally rare two-prior midpoint
modulus. It includes null reference states and infinite information ratios.
The audit rebuilt five modules, checked 225 declarations in 36 modules and
three exact types, and used only the standard axioms. Other dependencies used
cached objects with recorded source identities. Run
`python tools/verify_reference_absorption.py`; its four regression tests use
`test_reference_absorption.py`.

The [Bellman checkpoint](../results/information-bellman-20261030/README.md)
connects the recurrence to the actual count-flow information/work ratio. It
proves deterministic attainment, the unique price zero, continuity and strict
monotonicity, the exact singular-state criterion, and nonnegative information
increments with the exact continuation-flow identity. The audit rebuilt seven
modules, checked 189 declarations in 22 modules and five exact types, and used
only the standard axioms. Other dependencies used cached objects with recorded
identities. Run `python tools/verify_information_bellman.py`; its four regression
tests use `test_information_bellman.py`.

The [ordered-stopping checkpoint](../results/ordered-information-20261030/README.md)
proves aggregation of arbitrary measurable seeded, order-dependent capped
procedures into count flows with exact actual work. Midpoint information and
actual stopped-transcript Hellinger distance satisfy 4h <= I <= 8h, yielding
h <= K_N E_midpoint[T]/4, including null prefixes and procedures that take no
observations. The audit rebuilt eleven modules, checked 359 declarations in
47 modules and four exact types, and used only the standard axioms. Other
dependencies used cached objects with recorded identities. Run
`python tools/verify_ordered_information.py`; its four regression tests use
`test_ordered_information.py`.

The [adaptive-information checkpoint](../results/adaptive-information-20261030/README.md)
proves sharp squared-loss and RMS testing from affinity, including infinite
risk and zero endpoint densities. It transfers the midpoint bound to the
original arbitrary-seed, unrestricted-label adaptive population experiment,
with each physical flip charged once. Symmetric prior contraction scales
the target gap by s and the actual information ratio by s squared. The
resulting finite-prefix comparison is P_N <= 8T for a measurable prefix
estimate of uniform rare-prior RMS risk T. The audit rebuilt nine modules,
checked 498 declarations in 78 modules and seven exact types, and used only
standard axioms. Other dependencies used cached objects with recorded hashes.
Run `python tools/verify_adaptive_information.py`; its four regression tests
use `test_adaptive_information.py`.

The [finite-certificate checkpoint](../results/finite-risk-certificate-20261030/README.md)
proves all three unchanged finite stopping-program targets, including
`FiniteCertificateStatement`: R <= P_N <= 16R at the prescribed
N = ceil(64 max(B, rho B^2)). It includes the exact truncation penalty
rho sqrt(B/(N+1))/2 and the universal Bernoulli-label floor
min(rho, sqrt(rho/B))/16. The floor uses constant sign priors and does not
depend on the separate entropy-tail lower theorem. The audit rebuilt nine
modules, checked 559 declarations in 96 modules and eight exact types, and
found only standard axioms. Other dependencies used cached objects with
recorded identities. Run `python tools/verify_finite_risk_certificate.py`;
its four regression tests use `test_finite_risk_certificate.py`.

The [infinite-cap checkpoint](../results/infinite-cap-dual-20261030/README.md)
proves the exact attained four-prior dual, factor-three midpoint comparison,
factor-eight original minimax comparison, and monotone limits of ordinary
information and primal values. Its common compact moment image handles
singular reference states and infinite information. Positivity for rho <= 1/4
uses the Bernoulli-label floor. The audit rebuilt 14 modules and checked
68 declarations, eight exact types and only standard transitive axioms.
Other dependencies used cached objects with recorded hashes. Run
`python tools/verify_infinite_cap_dual.py`; regressions use
`test_infinite_cap_dual.py`.

The [genie-bracket checkpoint](../results/genie-brackets-20261030/README.md)
proves extended-value monotone ratio brackets, the finite-divergence residual
error bound, exact Bellman price certification and deterministic attainment.
Its full-cap reveal has exactly the latent divergence, so infinite latent
divergence makes every positive-cap genie ratio infinite. The audit rebuilt
nine modules, checked 101 declarations in twelve modules and eight exact
types, with only standard axioms. Other dependencies used cached objects
with recorded hashes. Run `python tools/verify_genie_brackets.py`; regressions
use `test_genie_brackets.py`.

The [genie-convergence checkpoint](../results/genie-convergence-20261030/README.md)
proves actual finite-prefix posterior information, latent-score reconstruction,
vanishing residual at finite latent divergence, and optimized convergence using
variance-reference regularization. It proves positive minimax brackets and
finite termination of the factor-sixteen stopping test for arbitrary laws,
0 < rho <= 1/2 and B > 0. It rebuilt twelve modules and checked
223 declarations in 33 Genie modules, twelve exact types and only standard
transitive axioms. Other dependencies used cached objects with source hashes.
Run `python tools/verify_genie_convergence.py`; its four regressions use
`test_genie_convergence.py`.

The [direct/conic checkpoint](../results/genie-conic-20261030/README.md)
proves the optimized piecewise direct squared-risk certificate, and the
finite atom SOCP with value exactly G_N^2 and at most 3 + 6m + (N+1)^2
variables. It includes zero scales, zero prices, singular references and
realization as globally admissible priors. Eleven new modules were rebuilt;
230 declarations in 35 Genie modules and nine exact types passed the audit.
Other dependencies were cached with source hashes.

The explicit infinite-divergence counterexample, manuscript integration and
final full audit remain in progress. Earlier checkpoints retain their scope.
