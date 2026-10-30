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

The general-law corollary's constants do not automatically give the separate
finite-law theorem's upper coefficient `30001`; that exact claim requires its
own derivation. Compiling deterministic ingredients does not establish any
statistical theorem.

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
  counts. This does not yet realize the marked Poisson estimator.
- `SurvivalWork.lean`, `LogSurcharge.lean`: geometric survival-work and scalar
  logarithmic surcharge estimates used in the remaining assembly.

The full deterministic quantile comparison passed the exact-target and
transitive-axiom audit on 30 October 2026: 20 modules, 121 declarations, two
frozen targets, and a rebuild of all 53 local dependency modules. The evidence
is in `results/entropy-tail-quantile-20261030/`. The observable statistical upper theorem and stopping-program
results are not yet proved by this branch. In particular, the comparison
alone is not a minimax characterization. No published verification claim has
been upgraded. The statistical lower bound remains assigned to the separate
cloud session.

An additional local checkpoint checked all 22 upper-construction modules and
the transitive axioms of all 188 declarations. Two independent exact-type
checks cover the population error theorem and Poisson second moment. Its
evidence is `.runtime/entropy-tail-upper-checkpoint-20261030/`; it used the
already compiled dependencies, recording all 184 local source hashes, and
did not rebuild that whole dependency closure. It is not the final upper
theorem audit. Remaining work includes integrating band costs and surcharge,
the cap schedule and mixed kernel sum, marked Poisson sampling in the actual
observable population experiment, and the approximation/minimax steps.

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
