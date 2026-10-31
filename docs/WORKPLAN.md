# Current work and completion ledger

Use this page to choose follow-up work. [RESULTS.md](RESULTS.md) records the
current mathematical scope; [VERIFY.md](VERIFY.md#choose-checks-by-task) maps
changes to checks. The detailed completion ledger is preserved below for source,
review, and CI history.

## Current priorities

| Area | Next work | Starting point |
|---|---|---|
| General-law rare-event results | Integrate the separately developed entropy-tail statistical lower theorem, then derive and audit the two-sided quantile characterization. Upper bounds, deterministic comparison, stopping programs and genie certificates have proofs; the final combined rebuild is in progress. | [Manuscript and audit](../paper/rare-event/README.md), [claim scope](RESULTS.md#general-law-rare-event-characterization) |
| Other paper-only results | Formalize the direct finite-gap lower argument, remaining rare-event regimes, and auxiliary envelope, smooth-density, and observed-state results. | [Finite-gap manuscript](../paper/finite-gap-rare-events/README.md), [results guide](RESULTS.md), [research index](../research/README.md) |
| Open research | Sharp rare-event confidence rates at and above the quadratic boundary; tighter constants and efficient selection algorithms. | [Current claim boundaries](RESULTS.md), [main overview](../README.md#scope-and-review) |
| Maintenance | Parameterize repeated entropy/base-cost and prefix-information/event-transfer arguments; extract shared audit code; simplify redundant premises and unused facts. These are non-blocking follow-ups. | [Recorded refactoring scope](#pr-10-review-and-maintenance-follow-up), [Lean map](../lean/README.md), [tool index](../tools/README.md) |

The [consolidated v6 manuscript](../paper/v6/README.md) presents all of
these results in one paper; the v5, general-law and finite-gap manuscripts
remain preserved as its sources. When a paper-proof result is formalized,
update the v6 verification section and rebuild the PDF.

The original RMS law, critical quadratic law, unbiased existence
characterization, confidence characterization, and canonical magnitude-oracle
lower bounds already have formal results with the scopes recorded in
[RESULTS.md](RESULTS.md). Preserve their specifications and evidence when
extending them. The Python toolkit remains outside the Lean proof.

Finite-law rate computation is now available in the
[rare-event calculator](../toolkit/README.md#3-compute-the-rare-event-rate-for-a-known-finite-law):
$O(n\log n)$ preprocessing and $O(\log n)$ evaluation or target-value
inversion, without subset search. The accompanying
[deterministic paper proof](RARE_EVENT_COMPUTATION.md) strengthens the
comparison to $\mathcal K\le Q\le(5/3)\mathcal K$ for all positive-gap laws.
Neither this comparison nor the Python calculation is Lean-checked. Exact
selection optimization, the executable general-law rare-event estimator and
the statistical formalization remain separate work.

For a new contribution, follow [CONTRIBUTING.md](../CONTRIBUTING.md) and
[AGENTS.md](../AGENTS.md). The project owner does not plan human specialist
review; its absence remains a stated limitation, not a pending completion gate.

## Completion ledger

The expandable record retains the earlier status descriptions, working rules,
source checkpoints, and CI outcomes. Read dates and commit identities with each
entry; earlier references to pending work describe that checkpoint.

<details>
<summary>Open the preserved verification and consolidation ledger</summary>

# Verification and consolidation

This ledger records the follow-up authorized on 27 October
2026. The starting published commit is `b3f88e6bc02b3d59ec9fe99529688e2bd911e1db`.
It preserves the full requested scope; a partial formalization does not complete
this plan. The original checkpoint is on `research/verification-consolidation-20261027`.

**Current status (29 October 2026):** the core verification and consolidation
package is complete and merged into `main`, through
[PR #10](https://github.com/davidiach/adaptive-threshold-estimation/pull/10).
The original RMS law and critical quadratic law are proved in Lean in both
directions; the exact Psi comparison, all-size extension, consolidated v5
manuscript, specialist packet, and process note are published.

The next contribution, the unbiased-estimation converse and its `I²/16`
lower bound, is now proved in Lean at `631886e`. All three completion gates
passed: the general two-distribution variance inequality, the information
bound in the existing observable adaptive experiment, and the inverse-moment
limit. The [full theorem](../lean/ThresholdHC/UnbiasedConverse/Full.lean) and
[audit](../results/unbiased_converse_001.json) cover the exact target and all
38 declarations. It was reviewed and merged in
[PR #13](https://github.com/davidiach/adaptive-threshold-estimation/pull/13)
at `d3dc500`, after all six branch/PR checks passed and no blocking findings
remained.

The 713 construction is now realized in the same observable model by
[one law-independent estimator](../lean/ThresholdHC/Observable713/Full.lean),
with uniform extended variance at most `23 I`, actual expected work at most
`31 I`, and product of separate suprema at most `713 I²`. Its second full
target combines the upper construction with the converse to prove unbiased
existence iff the inverse gap is integrable. The
[new audit](../results/observable713_001.json) checks both frozen targets and
all 47 declarations at proof checkpoint `15dbbda`.
The new realization was reviewed and merged in
[PR #14](https://github.com/davidiach/adaptive-threshold-estimation/pull/14)
at `45dde91`, after all six checks passed and no blocking findings remained.

The confidence characterization is now proved in the same observable model
at `d6feb30`: a lower coefficient `1/64`, an upper coefficient `8192`, one
family depending only on budget and failure probability, and explicit
nonvacuity. The model and full targets were frozen at `76e9a8f` before
supporting proofs. All three construction steps are complete: measurable
median amplification, exact execution of independent observable batches,
and the expected-work/radius comparison for every admissible budget.
The [full theorem](../lean/ThresholdHC/Confidence/Full.lean) and
[audit](../results/confidence_001.json) cover 18 modules, all 107 declaration
roots, and four frozen targets. It was reviewed and merged in
[PR #15](https://github.com/davidiach/adaptive-threshold-estimation/pull/15)
at `3aba9ee`, after all six checks passed and no blocking findings remained.

PR #12's toolkit was reviewed, repaired, and merged at `a7ed3b0` after all
10 checks passed on `d1f2191`. All 13 review threads were resolved, covering
numerical integration, binomial tails, invalid inputs, hangs, and overstated
planning claims. Its Python implementation remains outside the Lean proof.

The stronger RMS and confidence lower bounds are now proved for canonical
revealed and adaptively selected magnitudes at `4a5805c`. Their coefficients
are `1/64` and the paper's `15/(256 sqrt(2))`. The selected model has explicit
creation, revisit and stop operations, and a proved fresh-label/persistent-gap
interpretation; the revealed model grants the entire iid magnitude array.
The hidden experiment embeds unchanged. The [full theorems](../lean/ThresholdHC/OracleLower/Full.lean)
and [audit](../results/oracle_lower_001.json) cover eight frozen targets,
10 modules and 54 declarations, including minimax bounds and nonvacuity.
Models and targets were compiled and frozen at `3474a37` before supporting
lower-bound and semantic-embedding proofs. Publication and CI are recorded
on the focused oracle PR; local checks alone do not establish CI success.

The alpha > 2 rare-event RMS theorem is now proved in the same observable model.
The [full package](../lean/ThresholdHC/RareAboveTwo/Full.lean) covers all seven
frozen targets, including a single-coin family that is unbiased on every
power-margin law (second moment at most 28 rho in the proof), a law-independent
upper construction, a supported-law lower bound (coefficient 1/256 in the
proof), exact-power minimax and Psi rates, existence and nonvacuity.
The [scope guide](RARE_ABOVE_TWO.md) explains the proof and its conservative
constants. The [saved audit](../results/rare_above_two_001.json) passed at
`637fb4a`, covering 54 modules, 322 declarations and all seven frozen targets.
Publication and CI are recorded on
[PR #22](https://github.com/davidiach/adaptive-threshold-estimation/pull/22);
local checks alone do not establish CI success.

The 29 October
[finite-gap manuscript](../paper/finite-gap-rare-events/README.md), introduced
in [PR #18](https://github.com/davidiach/adaptive-threshold-estimation/pull/18),
supplies a separate paper-proof closed quantile law for known finite positive-gap
laws, global rarity and uniform expected observation budgets. It is not
Lean-checked or externally specialist-reviewed. General infinite-support
and unknown-law extensions remain outside its scope; this contribution does
not change the formal verification boundary above.

The next formalization priorities are the new general-law rare-event
characterization and stopping-program arguments, the remaining paper-only
rare-event results below two, and auxiliary envelope, smooth-density and observed-state
results. Sharp rare-event confidence rates at and above the quadratic boundary
remain open research.

**Rare-event manuscript update (29 October 2026):** the separate
[general-law manuscript, revised v2](../paper/rare-event/README.md), supplies an
entropy-tail characterization, an attained four-prior stopping dual, and
convergent genie certificates as audited paper proofs. The PDF, sources, exact
finite checks, and audit records are preserved together. Formalizing these new
general claims is follow-up work; finite certificates do not discharge it.
The current [claim scopes](RESULTS.md#general-law-rare-event-characterization)
record the pointwise finite-divergence qualification and sufficient-cap scope.

The project owner does not plan human specialist review. Its absence remains
a stated review limitation, not a pending task or completion gate. The four
maintenance refactorings below are non-blocking follow-up work. Historical
checkpoints and their original evidence scopes are retained below.

The unbiased-estimator review unit is [PR #4](https://github.com/davidiach/adaptive-threshold-estimation/pull/4),
based on that branch at `2162210`. The full critical upper proof is a further
focused unit on `research/critical-minimax-upper-20261028`, based on PR #4's
verified checkpoint `678e81c`. It is published as
[PR #5](https://github.com/davidiach/adaptive-threshold-estimation/pull/5) at
`c127478`. The separate Psi comparison is on
`research/critical-psi-comparison-20261028`, published as
[PR #7](https://github.com/davidiach/adaptive-threshold-estimation/pull/7) at
`eabf274`. The final manuscript and process update is on
`research/manuscript-completion-20261028`, published as
[PR #8](https://github.com/davidiach/adaptive-threshold-estimation/pull/8)
and based on PR #7.

The reviewer follow-up is split into [PR #9](https://github.com/davidiach/adaptive-threshold-estimation/pull/9)
for manuscript clarity and attribution, and
[PR #10](https://github.com/davidiach/adaptive-threshold-estimation/pull/10)
on `research/finite-gap-all-sizes-20261028` for the mathematical extension.
The latter removes the gap-count restriction at coefficient 1/4096, retains
the existing 1/512 large-count theorem, and supplies explicit single-coin
raw-moment and variance constants. It does not claim the same 1/512 constant
for all counts or an explicit final population minimax constant.

### PR #10 review and maintenance follow-up

The merge review repairs standalone v5 assembly and input-graph validation,
tests lock-file registration and dependency-set mutations, and corrects
notation, layout, scope and provenance in the manuscripts and current guides.
The corrected Lean docstring has a fresh audit record; the earlier record
and every target statement remain unchanged.

Four non-blocking refactoring suggestions are deferred to a separate cleanup:
parameterize the duplicated entropy-to-base-cost chain; parameterize the
prefix-information/event-transfer lemmas; extract a shared audit runner;
and remove the redundant scale-count lemma premise and unused intermediate
facts. These changes would reorganize proofs or statements without changing
the proved claims, and are not correctness defects in this PR.

## Current proof boundary

The original distribution-blind upper theorem is now proved against its
unchanged specification: one observable family satisfies the budget and RMS
bound for every gap law. The [full audit](../results/blind_upper_components_002.json)
includes almost-sure execution identities and every budget. The matching
critical rare-event upper is also proved against its frozen specification,
with coefficient 100000 in the original observable experiment. The exact
Psi formula, two-sided rate and counterexample are also proved; see the
[Psi audit](../results/critical_psi_001.json). The manuscript and review packet
now reference checkpoint `eabf274`; both have been rebuilt and visually checked.
Elapsed time and component counts do not establish completion.

The critical upper construction now has calibrated observable classifiers and
an unbiased random-level single-coin estimator under the full global rarity
constraint. Its actual population second moment is at most `28*rho`, and its
expected flip count is at most `112000000*criticalLogFactor(rho)`. Integrability,
population transfer and both bounds are proved; see
[the critical audit](CRITICAL_AUDIT.md#upper-construction-checkpoint).
Fresh-coin aggregation, its exact work/output identities in the original
experiment, and every budget regime are now proved. The unchanged
[full upper specification](../lean/ThresholdHC/CriticalUpper/Specification.lean)
is inhabited by [the final theorem](../lean/ThresholdHC/CriticalUpper/Full.lean).
The explicit comparison with the actual variational Psi objective now also
passes the frozen-target audit. The manuscript, process note and verification
guide now describe these completed proofs and their precise limits. Publication
and CI are tracked per PR; a local proof audit is not a claim that a later
GitHub Actions run has finished.

| Work | Completion evidence | Current state |
|---|---|---|
| Adversarial audit of the critical quadratic theorem | Trace every proof dependency, record objections and their resolution, distinguish paper arguments from kernel checks | [CRITICAL_AUDIT.md](CRITICAL_AUDIT.md) records the source audit, dependency checks, resolved proof obligations and review dependence; the full lower, upper and Psi statements now have separate kernel audits. This is not external specialist review |
| Specialist review package | Short overview, complete consolidated proof, precise questions, source and prior-art references | [Prepared](../paper/critical-review/README.md): four-page brief, two-page all-size addendum and complete proof, 20-page PDF compiled and visually checked; external specialist review is not planned |
| Formal critical argument | Exact statistical specification, proved dependency chain, kernel and axiom audit; scalar lemmas alone do not satisfy this item | The base-cost theorem, common hard pair, unrestricted critical minimax lower bound, and matching upper bound are proved in the original observable experiment for the full rare-prior class. See the [lower audit](../results/critical_components_016.json) and [full upper audit](../results/critical_upper_components_003.json). The [exact Psi formula, rate and minimax separation](../results/critical_psi_001.json) are also proved |
| Original distribution-blind upper bound | One budget-indexed observable algorithm independent of the magnitude/sign laws, realized in the original experiment; uniform work and RMS bounds; exact type and axiom audit | [Complete](BLIND_UPPER.md): the frozen full statement is inhabited by one budget-indexed observable family, with coefficient 512. Actual execution, almost-sure cost/output identities, uniform budget and RMS bounds are proved; exact-type and transitive-axiom audit passed |
| Consolidated v5 manuscript | Original minimax law, unbiasedness, 713 bound, rare-event regimes, critical result and correction to the Psi conjecture; accurate verification labels; compiled and visually checked | [Written](../paper/v5/README.md): 62-page manuscript including the all-size addendum, complete source-derived proof appendices, source checks and rendered-page review. Both critical bounds and Psi are linked at `eabf274`; the addendum's explicit constants are linked at `ebd3667`, the converse at `631886e`, the observable 713 construction at `15dbbda`, confidence at `d6feb30`, and the oracle lower bounds at `4a5805c`. No independent specialist review is claimed |
| General-law rare-event manuscript v2 | Standalone PDF and source identity, exact finite certificate replay, revision audit, and explicit claim status | [Added separately](../paper/rare-event/README.md): 55-page audited paper proof with the two editorial fixes. Existing manuscripts are preserved. `python tools/verify_rare_event_manuscript.py` checks identities and finite evidence; the new general theorems are not Lean-formalized |
| Process note | Reproducible account of construction, frozen statements, semantic review, failed approaches, reviewer dependence, and limits | [Written](process/METHOD.md) and refreshed at `6009662`, including completed realization proofs, the formula's freeze chronology, and lessons from the long run and focused PRs |
| Repository cleanup and publication | Clear current entry points, preserved source/evidence identities, passing relevant guards and CI, pushed commits and reviewable changes | The proof and manuscript stack through PR #10 is merged into main. README, results and verification guides lead to current evidence; historical bundles remain intact. CI results belong to each exact commit and are recorded in the corresponding PR |

## Working rules

* Preserve the existing frozen sources, imported manuscripts and historical
  evidence. Corrections should be conspicuous and must not silently rewrite
  what an earlier audit actually checked.
* Keep current mathematical explanations separate from chronological evidence.
  Reuse this ledger and the audit document rather than producing another package
  for every intermediate attempt.
* Record a failed proof or counterexample before changing course. If a claim
  fails, repair or qualify all current summaries that depend on it.
* A proved implication with a statistical hypothesis is not a proof of that
  hypothesis. Expose pending realization and probability steps explicitly.
* Push checked checkpoints. Do not label a run successful until its actual jobs
  have completed on the corresponding commit.

## Baseline verification

GitHub Actions [run 40488398325](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40488398325)
completed successfully on the starting main commit. This resolves the reviewers'
earlier observation that its run was still in progress. The new audit does not
turn those regression checks into verification of the critical paper theorem.

The original working tree contains pre-existing untracked research files. Work
here uses a separate Git worktree, leaving that material intact. No history
rewrite is planned to remove wording from old commit messages.

The published probability checkpoint `8e0124f9c2691163f015ceda93d5f01b29604def`
also passed all three Linux jobs in
[run 40494565796](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40494565796),
including its four scoped critical targets and the existing complete Lean
audits.

The finite-gap extension and updated specialist packet, published at
`071b650d928ba3fd35ff737ab2a455e8225f17e6`, passed all three jobs in
[run 40497825571](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40497825571),
including the five exact critical targets and all 63 declaration checks.
The later v5 consolidation has separate source, compilation, link, and visual
checks. Its numerical and research jobs passed in
[run 40499796986](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40499796986),
while the Lean job was cancelled after the subsequent push; that run is not
recorded as a full CI pass. The stopped-suffix checkpoint
`0bbd0ee7164b3b15aa2bda68466e5c0e25a6480f` passed all three jobs in
[run 40501696138](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40501696138),
including all six exact targets and 84 declaration checks.

The fixed-count restart checkpoint `af25e8827254f8ce9050cca409c7294ede0c64b8`
passed all three jobs in
[run 40504616018](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40504616018),
including its eight exact targets and 117 declaration checks. The subsequent
sign-test and estimator-entropy checkpoint `65131e6e782afebc6c320ca2b1b0010f4afb2a0d`
also passed all three jobs in
[run 40506853150](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40506853150),
including its ten exact targets and 135 declaration checks. The population
moment checkpoint `145a78519b58e84a01314da356b380882b644c5b` passed all three jobs in
[run 40510054032](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40510054032),
including twelve exact targets and 189 declaration checks. The good-gap
checkpoint `13435c1464e449bfc76225ac3d2544e9699e7e4f` passed all three jobs in
[run 40513347586](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40513347586).
The finite-scale checkpoint `891d5dc4e74d849cc93b100fbf99a28da112ccc3` also
passed all three jobs in
[run 40516081123](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40516081123),
including seventeen exact targets and 251 declaration checks. Later extensions
require their own CI results. The published base-cost and manuscript correction
checkpoint `5ba7166a6975e1d874e9166d9dbe015b90a5cbc5` passed all three jobs in
[run 40520815549](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40520815549),
including all twenty exact critical targets and 290 declaration checks.

The capped-transcript checkpoint `b054202c8a1958ca4b79e7021a9270e0e0f6da35`
passed all three jobs in
[run 40527378928](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40527378928),
including twenty-three exact critical targets and 351 declaration checks.

The population and observation geometry checkpoint `582f0f4491f729db999cb46cef4a372e62364f44`
passed all three jobs in
[run 40532725851](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40532725851).
The capped-policy risk checkpoint `1910216e77e0a39136dfed27fc5d199fe48d66a8`
also passed all three jobs in
[run 40539447152](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40539447152).
The common-pair checkpoint `d726b00d4ed552cc03e49a0eaf33cdedbb73ecbb`
passed all three jobs in
[run 40546208702](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40546208702),
including the full Lean audit and the research and numerical evidence jobs.

The unbiased-estimator checkpoint `678e81c` in PR #4 passed all three Linux
jobs in [run 40667339241](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40667339241).
The full-upper checkpoint `c127478` in PR #5 also passed all three jobs in
[run 40672110946](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40672110946).
The Psi and manuscript PRs report their own commit-specific CI results.

</details>
