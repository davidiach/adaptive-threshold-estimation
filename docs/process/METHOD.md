# How this research was developed and checked

This project combines written mathematical arguments, Lean proofs, and numerical
experiments. AI agents produced research, code and reviews under David Iach's
direction. The repository's [citation record](../../CITATION.cff) identifies the
human project lead. Agent review is not human peer review, and sharing a model
family can make apparently separate reviews fail in correlated ways.

The transferable part of the workflow is the separation between proposing a
claim, specifying it precisely, proving it, and checking that the specification
still expresses the intended problem. The [current results guide](../RESULTS.md)
states what has been established. This note explains how the evidence was made
and where it can mislead.

## Begin with the experiment, not the theorem name

For this problem, a correct inequality can become irrelevant if an algorithm
is given hidden magnitudes, if its budget excludes discarded pilot work, or if
its output is restricted without justification. Similarly, proving a statement
for a fixed finite inventory of coins does not automatically prove it for a
reservoir with adaptive creation.

The formal development therefore progressed through explicit transcript models.
The final [Tier 6 model](../../lean/ThresholdHC/Tier6/AlgorithmModel.lean) defines
uniform expected work, retains infinite squared error, and takes a minimax
infimum over observable randomized adaptive estimators. Its process realization
is a proved conclusion. Nonempty budget classes and a finite-risk witness check
that the main statement is not vacuous. These semantic checks matter as much as
the final kernel acceptance.

The corresponding upper-bound task has an additional quantifier requirement:
one algorithm must work across magnitude laws. An existence theorem allowing a
different law-dependent algorithm for each law would leave that task unfinished.

The critical single-coin development also distinguishes real expectations from
extended nonnegative moments. Lean's real integral is totalized, so it must not
silently stand in for an expectation without integrability. The
[population model](../../lean/ThresholdHC/CriticalEntropy/PopulationModel.lean)
retains infinite second moments and work; its signed mean identities require
finiteness that implies integrability. A common uniform random tape constructs
the parameterized Bernoulli laws and proves measurability of conditional
quantities. The hidden parameter enters that generator, never the procedure's
seed or observation interface.

The same issue arises for variance: Mathlib's ordinary real variance converts
an infinite extended variance to zero. The
[variance-to-moment bridge](../../lean/ThresholdHC/CriticalEntropy/PopulationVariance.lean)
therefore requires bounds on extended variance and derives square integrability
before using real-valued identities. This is a semantic safeguard, not an
additional assumption about the algorithm's output.

The critical single-coin base-cost theorem now composes that probability model
with activation normalization, observable restarts, good-gap selection and a
rarity-dependent scale count. Its exact specification quantifies one universal
constant before the rarity and procedure, and charges all-negative population
work. The common population pair and its finite interactive transfer are now
proved. The full minimax transfer still needs arbitrary population seeds,
unrestricted creation and the termination limit. The verification record keeps
those completion flags separate.

The capped-observation reduction checks a further semantic boundary. Replacing
the full transcript by stopping time and head count is justified by proving
the full seed/word density, population-independent conditional reconstruction,
canonical Hellinger affinity preservation, and exact work preservation.
An equality for an invented finite probability vector alone would not establish
this reduction. Impossible cells are identified explicitly, and the finite-cap
assumption remains visible in the exact targets.

Compactness is now checked against the actual population class as well. The
formal proof uses the weak dual of `L²`, recovers bounded measurable priors by
Riesz representation, and proves that every admissible prior is covered. The
target integral is retained as a separate finite coordinate: two populations
may have the same observation law and different targets. Continuity and
convexity of the actual Hellinger constraints are then derived from the
likelihood formulas. The finite convex RMS comparison now uses those actual
coordinates, restricts to the common support, and transports its estimator back
to the observable procedure with unchanged work. The exponential-moment proof
establishes square integrability before bounding RMS.

The formal proof also uses a narrower construction than the paper's general
additive-component reduction. For repeated copies of one policy, the minimax
score can be symmetric: `F=c+sum_i u(Z_i)`. Then `Z=n u(Z_1)+c` has the same
mean and variance `n Var(F)`, proved under the actual iid law. This suffices for
the policy-specific pair and avoids importing the more general component
randomization argument.

The common-pair extension proves the statistical quantifier interchange.
First a repetition argument converts the policy-specific affinity bound to
a normalized distance/work constraint, including zero null work. Then a finite
revealed policy mixture is constructed using product seed spaces, and its
affinity and work are proved to be the weighted averages. Enlarging caps and
adding independent seed coordinates preserve the canonical affinity. Compactness
now selects one population pair before every capped-policy quantifier. This
does not by itself establish the simulation of interacting population algorithms.

That simulation is now constructed for every fixed finite family and horizon.
The independent-tape law is derived from one-step tape splitting and matched to
the existing finite transcript probabilities. Replacing one genuine tape gives
the exact hybrid law. Each local simulator is an observable stopped procedure,
and its actual population expected cost is charged to the full flip count.
This checks the probability interpretation and work accounting as well as the
algebraic Hellinger decomposition. Arbitrary population seeds and unbounded
creation remain separate completion requirements.

## Freeze established questions and preserve corrections

The original [brief](../../BRIEF.md) required fixed target statements and
scorers. Source hashes bind the question as well as the answer. Later extensions
use separate specifications and manifests, with changes and authorizations
recorded in the [freeze log](../../FREEZE_LOG.md).

A hash proves file identity, not mathematical truth. Freezing an incorrect
model would preserve the mistake. The useful order is to inspect definitions,
check elaboration, challenge assumptions and quantifiers, and then freeze the
target used to evaluate the proofs. A new specification introduced alongside
its proof must not be retrospectively described as a target frozen beforehand.

Historical manuscripts and reviewed bundles remain available. A subsequent
correction belongs in the current explanation with a link to the old record;
silently replacing the old bytes would destroy the evidence of what was checked.

## Use each check for the question it can answer

| Evidence | What it establishes | What it does not establish |
|---|---|---|
| Lean elaboration and kernel checking | The supplied term proves its precise formal type | That the type faithfully models the scientific claim |
| Exact-type and transitive-axiom audit | The registered statement is inhabited using the allowed axioms | Correctness of unformalized neighboring arguments |
| Source locks and clean replay | Which sources and commands produced a result | Independent mathematical review |
| Exact finite experiments | Identities or inequalities for those enumerated experiments | A continuum or unbounded-horizon theorem |
| Held-out simulations | Empirical performance on the specified data and budgets | Uniform statistical rates or practical superiority in other settings |
| Paper review | A reader's reconstruction and objections for the inspected argument | Kernel verification or guaranteed independence |

A rendered-page review caught a manuscript assembly error that compilation
and source hashes had missed: globally prefixing parenthesized equation tags
also changed arguments such as `q(D)`, `R(B)` and `mu(E)`. The original proof
sources were intact. The builder now protects mathematical expressions, and
regression tests check the restored formulas as well as renamed references.
Source identity and successful typesetting alone do not establish faithful
assembly of a new document.

The formal guards reject incomplete axiom output and unsuccessful processes,
rather than accepting a log merely because it contains some successful lines.
Their regression tests exercise failure cases. Toolchain and Mathlib revisions
are pinned. A successful CI run is attributed to its exact commit and actual
completed jobs; an in-progress run is not evidence of success.

## Failed approaches changed the mathematics

The [off-grid bias audit](../../proposals/constants/BIAS_AUDIT.md) shows why a
better finite-grid score cannot replace a uniform bound. The accepted 713 result
instead has a separate analytic argument and formal specification. Its constant
is an upper bound, not a claim of optimality.

The rare-event continuation proposed a variational characterization using Psi.
The later critical quadratic argument claims an additional scale-entropy factor.
If that argument is correct, the statistical characterization fails while the
formal optimizer of the variational problem remains correct. This distinction
prevents a failed conjecture from being confused with a faulty optimizer proof.

The critical proof's [attempt record](../../research/2026-10-27-nonlinear-critical/attempts.md)
also records why a direct additive-estimator comparison did not settle general
interaction. The successful paper route instead needs null-population cost,
a common hard pair, and midpoint simulations. Each bridge has to be justified;
repeatedly checking the easier endpoint calculation cannot substitute for it.

## Review dependence and human responsibility

Separate construction and adversarial review roles can expose mistakes, but the
number of agent reviews is not a count of independent scientific validations.
The critical theorem's [second review](../../research/2026-10-27-nonlinear-critical/second-review.md)
discloses its author's contribution to the base-cost argument. That author can
cross-check other components but cannot independently certify their own work.

Primary-source comparisons must inspect assumptions, cost definitions and
normalizations. A nearby theorem's title is insufficient. The source records
credit established sign-entropy, convex-estimation and Hellinger-decomposition
methods. A targeted literature check does not establish priority.

A human specialist review remains a distinct step. A useful review package
states the experiment, strongest claim, proof dependencies, and specific places
where an objection would break the conclusion. No reviewer should have to infer
the current theorem from chronological run logs.

## Keep the evidence navigable

The main reading path is the manuscript and results guide, followed by the
precise specification or proof. Historical logs, raw samples and failed attempts
remain supporting records. Fresh verification output goes to disposable or
ignored directories so it cannot overwrite a published checkpoint by accident.

The [active completion ledger](../WORKPLAN.md) and
[critical follow-up audit](../CRITICAL_AUDIT.md) distinguish completed components
from remaining work. As of this note, the original upper theorem, the complete
critical statistical argument, and external specialist review must not be
described as completed formal verification. More proof lines or larger logs
would not change those boundaries on their own.
