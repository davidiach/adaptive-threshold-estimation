# Research hill-climb report

## Current critical-regime checkpoint — 27 October 2026

**The unrestricted alpha=2 Psi conjecture remains open.** The new
[paper theorem](../../research/2026-10-27-critical-two/construction.tex)
characterizes the minimax rate of noninteractive additive estimators at the
fixed quadratic law $F(d)=(4d)^2$:

$$R_{\rm add}(B)\asymp\min\{\rho,\sqrt{\rho L(1+\log L)/B}\},\qquad L=1+\log(1/\rho).$$

The class includes heterogeneous single-coin procedures, shared independent
randomness, and an unbounded finite-mean number of coins selected before
observations. Each component may stop at an unbounded time using its own
coin history. Its terminal output is an additive sum; the note states the
separate square-moment and work conditions. Nonlinear aggregation and
decisions using other coins' observations remain outside this lower bound.
Thus the extra iterated logarithm is necessary in this class; it has not been
proved necessary for unrestricted population estimation.

The central new product theorem covers every single-coin procedure with
uniform bias at most $\rho/64$ and arbitrary variance/work allocation. A
seed reweighting argument extends it to the additive population class. The
matching upper construction was already present in the separately owned
[critical upper note](../../research/2026-10-27-minimax-audit/theorem/critical.tex)
and is credited explicitly. The new argument is a **paper proof with two
separate agent reviews**, not a Lean theorem, external specialist review or
priority certification. See the [checkpoint and exact scope](../../research/2026-10-27-critical-two/CHECKPOINT.md).

All 34 current guard regressions pass; 311 protected baseline paths and 65
lock entries are unchanged. Exact scalar checks and all nine finite Fisher
diagnostics replay successfully, with their limitations recorded. No old
verification record or other owner's Tier5/population work was overwritten.
The useful change was a lower bound for an entire estimator class rather than
further tuning of its likelihood dictionary. The next unresolved step is to
control nonlinear or interactive estimators, or construct one attaining Psi.

## Previous alpha>2 checkpoint — 27 October 2026

**New mathematical result: paper proof with two separate agent reviews.** For
the exact power margin $F(d)=(d/a)^\alpha$, the previously unresolved regime
$\alpha>2$ now has the matching rare-event RMS rate

$$R_{\mu,\rho}(B)\asymp_\alpha\min\{\rho,\sqrt\rho/(a\sqrt B)\}.$$

The [complete TeX note](../../research/2026-10-27-route-a/construction.tex) gives
an observable asymmetric classifier and unbiased randomized correction, with
second moment at most $(153/56)\rho$ and separate mean work at most
$w_\alpha/a^2$. It handles every measurable $q$ with $\int q\,d\mu\le\rho$;
the sharp rarity-weighted inverse-square integral is the step that removes
the extra logarithm. Exact expected-budget replication and saturation are
proved. The upper bound also holds for the corresponding margin-envelope
class without knowing its individual law. The matching lower bound imports
the precise Lee–Valiant inputs through an explicit fixed-gap simulation.

The [contract](../../research/2026-10-27-route-a/CONTRACT.md),
[edge cases and failed approaches](../../research/2026-10-27-route-a/EDGE_CASES.md),
[source refresh](../../research/2026-10-27-route-a/sources.md), and
[two](../../research/2026-10-27-route-a/review.md)
[reviews](../../research/2026-10-27-route-a/second-review.md) delimit the result.
This is not an arbitrary-law theorem, an $\alpha=2$ solution, a Lean proof of
the new rate, external specialist review, or a certified priority claim.
Constants depend on $\alpha$ and diverge near two. The strongest failed
construction charged logarithmic rarity work on every negative coin; the
successful construction charges it only on positives and integrates that cost
under the global rarity constraint. The next precise question is how to replace
the inverse-square work argument at the critical exponent without introducing
an extra budget logarithm.

**Formal foundation, not a new constant.** A separately reviewed and locked
[Lean bridge](../../research/2026-10-27-route-a/formal-audit.md) exports
$\mathbb EY^2\le23I$, $\mathbb EW\le31I$, and the non-strict product of separate
suprema at most $713I^2$ for the existing fixed kernel/estimator model. Five
public roots pass exact-type and transitive-axiom checks. Fresh-coin realization
of that kernel family remains outside this formal theorem.

The [baseline ledger](../../research/2026-10-27-route-a/BASELINE.md) records the
actual checkout/renamed remote, concurrent documentation commits, locks,
existing evidence and replay. Tier4 was already complete when this session
started: its full infinite tape KL still uses a fixed finite coin family.
Older open-work descriptions below record their historical checkpoint.
Published verification records and imported sources were preserved. Existing
numerical/integrity gates and all 26 validation tests passed in a byte snapshot;
the benchmark replay passed after making the existing ignored Python runtime
available. Eighteen new exact finite-prefix classifier checks retain unresolved
tails. Historical CI is not claimed as verification of this new state.

**Retrospective.** The useful change came from attacking the estimator's noise
and work allocation, not from adding formal proof lines. Parallel construction,
source/adversarial review, and formal-foundation roles were separate; model
diversity is not guaranteed. The new formal work stayed subordinate to the open
statistical question. No remote publication or external contact occurred.

## Environment and evidence

The Lean track ran: Lean 4.36.0-rc1 with Mathlib pinned to
`9bdd0bc71aaae0fd83889f9aacd70c32fccd1bcd`. All 33 supplied statements
compiled unchanged and passed their numerical sanity checks. Twelve files
were frozen in commit `8128f9a`. The approved Tier 2 extension added nine
locks in `f86a9ba`, as recorded in [FREEZE_LOG.md](../../FREEZE_LOG.md); the original target
syntax and mathematical meaning are unchanged. All 50 original input
files match the supplied manifest.

Python 3.12, NumPy 2.4.4, SciPy 1.17.1, mpmath 1.3.0, and Numba 0.68.0 were
used. Dependencies are pinned. Public checkpoint history is at
[davidiach/adaptive-threshold-estimation](https://github.com/davidiach/adaptive-threshold-estimation).

Final proof checkpoint `a485ad6` also passed the independent
[Linux CI run](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40410461304):
all 33 frozen targets, the seven additional scalar lemmas, numerical checks,
original input hashes, and locked experiment provenance. The proof score is
therefore reproduced on Windows and Linux.

## A — Lean proofs

**Tier 2 integrated and verified locally, 27 October 2026.** The target set now contains
the original 33 proved targets plus 13 new targets worth 61 points. The
validated integration baseline is 60/121 (Tier 1 60/60, Tier 2 0/61). The proposed
Tier 2 mathematical statements are unchanged. Scorer v2 requires a successful,
complete audit and rejects unexpected axioms even when accompanied by `sorryAx`.
The Tier 2 numeric checker requires positive coverage and includes a deterministic
I6 test. See [TIER2.md](TIER2.md) and the approval/validation record in [FREEZE_LOG.md](../../FREEZE_LOG.md).

**Tier 2 complete: 80 → 121/121, all 46 targets.** Checkpoint 001 proved
I1–I4, I7, K3, and R1. Checkpoint 002 adds I5–I6 and K1–K2/K4–K5, completing
all 13 Tier 2 targets (61/61) while preserving Tier 1 (60/60). Full build,
all 21 frozen hashes, exact target types, and both 46-report audits pass
locally. No `sorry` remains in either tier's proofs, and the axiom union is
exactly `propext`, `Classical.choice`, and `Quot.sound`. Evidence is saved
under `results/lean_tier2_002*`. Commit `e6cbd9c` also passes the independent
[Linux replay](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40417194219):
121/121, 46/46 targets, 7/7 scalar lemmas, and 130/130 roots for the full 713
theorem. Both the Lean and numerical/validation CI jobs succeeded.

The information proof factors each transcript likelihood by coin, derives
the next-query posterior, and handles zero histories and deterministic-coin
endpoints explicitly. A finite chain-rule induction charges KL only for
actual queries; data processing then yields the testing lower bound.
This covers the frozen finite deterministic-policy, bounded-horizon model.

The classifier proof identifies the exact finite `streamProb` sums with
Bernoulli tape expectations, proves equality with the stopping implementation,
and derives concentration, error, work, and moment bounds. Both signs, strict
stopping tests, negative ties, shared prefixes, and Bernoulli endpoints are
covered. R1 follows from a supporting-line inequality at the stipulated
atomic cutoff. Independent agent reviews found no semantic mismatch in these
boundary cases. The complete 713 guard also passes again at 130/130 roots.

**Proved and machine-checked: 0 → 34 → 60/60, all 33 targets.** Checkpoint 002
passed the full build, frozen hashes, exact target types, and independent
audit with exit zero and all 33 reports. The axiom union is exactly
`propext`, `Classical.choice`, and `Quot.sound`. No `sorry` remains in the
Tier 1 proof modules. No Tier 1 targets are parked or unproved. This verifies the
specified targets, not every theorem of the research papers. Evidence is in
`results/lean_score_002.json`, `results/lean_checkpoint_002.json`, and
`results/lean_independent_audit_002.log`.

The original scorer omitted its audit subprocess exit status from validity.
The approved v2 scorer now checks exit status and all 46 target reports directly.
`tools/verify_lean_checkpoint.py` retains the independent audit, consistency
check, and no-regression requirement. Linux CI replays it.

**Full 713 extension: proved and machine-checked.** The separate development in
`lean/ThresholdHC/Uniform713/` proves `full_bound_713` against the exact
`FullBound713Statement` recorded before the final proof. The theorem derives
concentration from independent bounded observations, analyzes the actual capped
classifier and shared-prefix cost, constructs the independent geometric level,
and establishes square integrability, finite expected work, unbiasedness, and
the strict product bound for arbitrary magnitude/sign laws. The model assumes
only measurable independent [0,1] observations with mean 1/2 ± d, 0<d≤1/2, and
integrable 1/d. Bernoulli observations are included. No desired error or moment
bound is assumed. A concrete Bernoulli(1) example verifies that the assumptions
are satisfiable. The separate guard audits 130 public proof roots, checks the
recorded specification hash and all local specification dependency hashes, and
requires the complete theorem in CI. Its guard, manifest, specification, and
definition-bearing dependency files are included in the approved 21-file freeze.

Full proof checkpoint `852690a` passed the independent
[Linux CI run](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40414013439):
all 130 proof roots, the exact full theorem type, the original 33 targets,
scalar checks, numerical checks, and provenance locks. This verification is
for that committed checkpoint; later proposals are separate work.

## B — Constants

**Numerical evidence.** Both candidates were chosen from 169 development-only
trials and published in `f4f8e84` before their held-out evaluations.

| Configuration (k1,k2) | Dev proxy | Held-out proxy | Decision |
|---|---:|---:|---|
| Original (1,1) | 6.778762 | 6.771882 | Baseline |
| (0.25,1) | 5.550646 | 5.550060 | ACCEPT |
| (0.25,0.5) | 4.281742 | 4.282069 | ACCEPT on finite grid |

**Proved in Lean; also independently reviewed on paper.** For (0.25,1),
conditional second moment is below 23/d and expected work below 31/d. Thus
the untruncated estimator has
`Var(Y) E[W] < 713 (E[1/D])^2` when `E[1/D]` is finite, improving the supplied
analytic upper constant 12665. See the full
[713 proof](../../proposals/constants/UNIFORM_PRODUCT_BOUND.md) and
[independent review](../../proposals/RESEARCH_REVIEW.md). The complete proof is
`lean/ThresholdHC/Uniform713/FullBound.lean`; its audit is
`results/uniform713_status.json`. The earlier seven scalar lemmas remain
separately reproducible. Optimality is not claimed; the lower bound 1/16 and
finite-grid proxy remain different objects.

**Proved counterexample.** The finite-grid winner (0.25,0.5) fails the original
uniform bias bound: at d=0.1 and cap 2^97, a specific all-tails event exceeds
that bound by a factor greater than 2907. Its grid score therefore cannot be
used as a universal guarantee. See [bias audit](../../proposals/constants/BIAS_AUDIT.md).

## C — Direct-real benchmark

**Numerical evidence — REJECT.** The final candidate was locked in `6eec012`,
then tested once with 500 repetitions per cell. No post-test tuning occurred.

| Budget | Method | RMSE, descriptive 95% interval | Mean work, descriptive 95% interval |
|---:|---|---:|---:|
| 16,384 | GHA | .02990 [.02778,.03204] | 15,893 [15,619,16,167] |
| 16,384 | Direct-real | .03910 [.03260,.04563] | 15,329 [14,467,16,205] |
| 65,536 | GHA | .02012 [.01862,.02159] | 66,847 [65,667,68,031] |
| 65,536 | Direct-real | .02185 [.01838,.02581] | 64,658 [62,853,66,586] |

GHA has the lower point estimate at both budgets; the larger-budget comparison
does not resolve a separation statistically. Constant zero has RMSE .025,
beating both smaller-budget point estimates. Outputs are clipped to [0,1],
and the real-valued variance boundary is heuristic for this unbounded model.

The selected method uses randomized level sums and independent two-success
calibration; it exercises two levels. New training plus tuning cost was
**1,541,656,608 draws**, compared with reused GHA training of 166,827,744 and
GHA-only tuning of 34,093,824. These are amortized comparisons, not equal-total-
cost experiments. Implementation checks covered 71,049 finite tapes, 1,000
telescopes, and 10 repeated-calibration identities. See [Track C](TRACK_C.md)
for raw-error results, seeds, offline-cost breakdown, and calibration proof.

## D — Source audit and remaining theory

**Source comparison.** Lee–Valiant Corollary 19's small-parameter conditions,
Hellinger normalization, and original-prior expected-work denominator match
the supplied note. Its large-gap extension is explicitly a separate argument.
No mathematical correction to the imported input was needed.

**Proved on paper.** Exact power-margin classifier-envelope integrals were
derived for alpha at and above two. A separate argument rules out an exact,
fully uniform unknown-rarity guarantee with no additive error floor, already
for a known fixed gap. Both arguments and their qualifications are in
[Track D](TRACK_D.md). The adaptation argument was independently reviewed.

**Numerical evidence.** Twenty-five deterministic quadrature checks passed;
27 cases evaluate the existing upper bracket. These do not establish a
matching upper theorem for alpha>=2 or arbitrary laws.

## Tier 3 landmark

The separately locked Tier 3 specification contains ten component statements
and one conjunction theorem. It extends the existing finite model to arbitrary
measurable random seeds and seed-dependent tests, then to unbounded observation
horizons with finite expected actual work under the plus hypothesis. The
unbounded model identifies all joint finite-prefix laws explicitly; it does
not assume a KL bound, convergence of tests, or almost-sure termination.
Its targets derive almost-sure termination under both hypotheses and the
terminal testing lower bound. A geometric-seed experiment establishes that
the specification is realized by a process with genuinely unbounded work:
its work is N+1, has finite expectation, and exceeds every finite cap with
positive probability. The realization theorem covers every sign prior in [0,1].

The optimizer target covers an arbitrary probability space and measurable
positive magnitude bounded by one half, allowing atoms and singular laws and
assuming no inverse moment. It proves the unique cutoff, feasibility and
optimality for every positive parameter, saturation, and the three-region
integral identity.

Checkpoint 001 proved randomized transcript normalization, the integrated
conditional information/work inequality, cutoff existence/uniqueness, and
the full arbitrary-law optimizer. Checkpoint 002 completes all eleven exact
targets: ten components and `tier3_landmark`. The separate audit passes
**152/152 declaration checks**, with only `propext`, `Classical.choice`, and
`Quot.sound`; no pending targets or proof stubs remain. Eight audit regression
tests pass. The original 21-file freeze and the separate nine-file Tier 3
specification lock both verify. The existing 121-point target set is retained,
and the full 713 audit passes again at 130/130. The independent
[Linux replay of `23988c7`](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40468287646)
confirms 11/11 Tier 3 targets and 152/152 declarations, the original 121/121
score, 7/7 scalar lemmas, and the complete 130/130-root 713 audit. Both CI jobs
passed, including the numerical checks and both validation regression suites.

The randomized proof derives integrability by factoring finite-horizon policies
and tests through finite codes. Marginal KL and tests with global error bounds
follow from integral log-sum inequalities. The unbounded proof derives valid
policy paths and almost-sure halting from finite expected work, transfers that
property to the other hypothesis using bounded prior ratios, and proves
convergence of bounded terminal acceptance events. Independent agent reviews
found no hidden termination, convergence, information, or inverse-moment
assumption in the specified conclusions.

| Component | Proof entry point |
|---|---|
| Arbitrary-seed marginal KL and testing | [Randomized.lean](../../lean/ThresholdHC/Tier3/Randomized.lean) |
| Finite work and almost-sure halting | [StoppingBase.lean](../../lean/ThresholdHC/Tier3/StoppingBase.lean) |
| Unbounded terminal testing | [Stopping.lean](../../lean/ThresholdHC/Tier3/Stopping.lean) |
| Arbitrary-law optimizer and cutoff | [Optimizer.lean](../../lean/ThresholdHC/Tier3/Optimizer.lean) |
| Explicit unbounded experiment | [Examples.lean](../../lean/ThresholdHC/Tier3/Examples.lean) |
| Combined locked landmark | [Full.lean](../../lean/ThresholdHC/Tier3/Full.lean) |

This development still has a fixed finite set of coin magnitudes in the
transcript model. Its unbounded result concerns stopping and terminal testing;
it does not claim a measure-theoretic KL identity for the entire infinite
transcript. The optimizer result is a variational identity, not a matching
arbitrary-law minimax upper theorem.

## Open work and proposals

- Tiers 1 and 2 and the separately specified Tier 3 landmark are proved.
  Extending the transcript model to countably many coins and identifying the
  measure-theoretic KL of the entire infinite transcript remain further work.
- The full 713 probability theorem is already proved and separately audited;
  adding it to the scored target list remains a separate scope decision.
- The arbitrary-law matching upper bound and matching alpha>=2 constructions
  remain open here. No general distribution-blind theorem is supplied.
- Unknown-rarity algorithms need a qualified guarantee, such as an additive
  floor or restricted parameter range; two-success work calibration alone
  cannot avoid the stated obstruction.
- Scorer v2 incorporates audit exit status directly; the independent audit
  remains a second check under the approved Tier 2 freeze.

No novelty, priority, external-referee endorsement, or universal superiority
claim is made.

The user's ETH preprint was assessed as an indirect algorithmic research lead;
no result here depends on its claimed theorem. See
[relevance assessment](../../proposals/ETH_PAPER_RELEVANCE.md).
