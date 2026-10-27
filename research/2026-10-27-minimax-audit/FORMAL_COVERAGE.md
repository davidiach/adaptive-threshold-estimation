# Formal coverage at this research checkpoint

Pinned HEAD: `ddf950122776a059e62c808021bbd2b59c39f0b0`. The initial working tree
also contained the uncommitted Route A bridge and research, plus documentation
edits. Those are inherited work, not results first established by this run.
No historical theorem, freeze manifest, validator, or acceptance criterion is
modified. All new audit outputs are under `formal/`.

## What the current sources actually say

| Paper/headline statement | Exact formal counterpart or component | Coverage limit |
|---|---|---|
| v4 Theorem 1: arbitrary-law minimax RMS and confidence, distribution-blind upper | No exact algorithm-level declaration. Scalar modulus lemmas, classifier and calibration components, and finite-family information roots support parts. | Full iid-reservoir minimax quantifiers and replication are not assembled in Lean. |
| v4 Theorem 2: unbiased existence iff inverse first moment is finite | Sufficient construction: `ThresholdHC.Uniform713.full_bound_713 : FullBound713Statement`. | The converse for every admissible unbiased algorithm is unformalized. |
| v4 Theorem 2: uniform product lower bound I²/16 | Scalar two-point/Hellinger and fixed-gap components in `ThresholdHC.Proofs`; no exact uniform converse declaration. | Product of two suprema is not a pointwise product. |
| Unbiased construction with product <713 I² | `ThresholdHC.Uniform713.full_bound_713`. | Arbitrary latent probability law, measurable conditional observation kernel, independent bounded [0,1] observations with means 1/2 +/- d, integrable 1/d. No iid-reservoir policy realization conclusion. |
| Separate uniform moment/work bounds | `ThresholdHC.ResearchRouteA.separate_moment_bounds` and `uniform_family_bounds`. | Fixed conditional kernel/observables, nonempty family of latent laws with common inverse moment. Formal upper bounds on two separate suprema; not a new rare-event theorem. |
| v4 stopped transcript KL, bounded finite experiment | `ThresholdHC.Proofs.stopped_transcript_kl : ThresholdHC.Targets.stopped_transcript_kl`. | Deterministic policies, finite `Fin m` coin family, bounded horizon, fixed gaps. |
| Randomized and unbounded stopping/testing | `ThresholdHC.Tier3.unbounded_stopping : UnboundedStoppingStatement`; `unbounded_testing : UnboundedTestingStatement`. | Arbitrary measurable seed and unbounded time, but fixed finite `Fin m` coins and specified finite-prefix realization. The one-law-to-two-law stopping transfer depends on finite m. |
| Genuine full infinite-transcript KL | `ThresholdHC.Tier4.infinite_kl_bound : InfiniteKLBoundStatement`; also `infinite_kl_eq_iSup`, `infinite_kl_finite`, `observable_kl_bound`. | Mathlib measure-theoretic KL of seed and full padded tape; still fixed finite coin family with symmetric sign priors and fixed gaps. This tier is complete, not a pending full-KL task. |
| Arbitrary-law rare-event cutoff and optimizer | `ThresholdHC.Tier3.arbitrary_law_cutoff : ArbitraryLawCutoffStatement`; `arbitrary_law_optimizer : ArbitraryLawOptimizerStatement`. | Measurable D in (0,1/2] a.e., probability measure, 0<rho<1, every measurable feasible allocation. Includes atoms/singular laws, no inverse moment needed. It is a variational identity only. |
| Rare-event arbitrary-law minimax lower bound Psi | None. | Paper proof imports Lee--Valiant Corollary 19 and applies a hybrid decomposition; the rare-prior theorem is not formalized by symmetric Tier 4. |
| Matching 0<alpha<2 rare-event power laws | None as a full statistical theorem. | Paper proof with alpha-dependent constants. |
| Matching alpha>2 rare-event power law | None. | Inherited uncommitted Route A paper proof, not this run's result. |
| New alpha=2 upper with controlled iterated logarithm | None. | New reviewed paper proof only; no matching theorem claimed. |
| v4 envelope, gap, polynomial-margin, refined-log corollaries | Scalar integration/modulus components only; no exact full corollary declaration. | Full statistical assembly unformalized. |
| v4 nonnegative unbiased impossibility | None. | Paper absolute-continuity argument. |
| v4 smooth-density robustness | None. | Paper hard-pair class and derivative bounds. Smooth latent density is not cross-state regression regularity. |
| v4 finite-cell and continuous-magnitude observed-state obstructions; nested log² lower bound | None. | Paper priors on fixed deterministic sign arrays, observed-state oracle and scale-uniform class verification. |
| Unknown-rho impossibility | None. | Paper finite-stopped-transcript equivalence; excludes deterministic endpoint in its stated argument. |
| New countable-reservoir termination counterexample and correct testing bridge | None. | Paper proof plus exact finite arithmetic checks. It refutes a proposed stronger scope, not an existing Lean theorem. |

The exact optimizer's split is `D<=h`, `h<D<=t`, and `t<D`, so endpoint masses
are neither lost nor duplicated. Its assumptions exclude D=0 and include D=1/2.
Tier 4's realization condition describes actual finite-prefix laws; it does
not assume the desired KL inequality. The 713 model assumes observation and
inverse-moment conditions, not its estimator's conclusion.

## Concurrent Tier 5 work observed during this run

At 08:33 UTC on 27 October 2026, untracked `lean/ThresholdHC/Tier5/`, its
separate lock, target manifest, verifier, and validator tests were visible and
changing. They were not authored by this task. Their contemporaneous hashes
are in `formal/concurrent_tier5_snapshot.json`. Current HEAD had also moved
through concurrent commits `d4f74a2` and `db25e62`; the initial HEAD remains the
pinned starting point, not a claim about the whole final checkout.

The inspected Tier 5 specification uses natural-number coin labels and a
measurable magnitude environment included in a common seed, with conditional
finite-prefix laws. Its `CreationStopsStatement` correctly asserts stopping
only under the law with finite expected work. Its complete-landmark manifest
contains nine targets. Several target declarations were present, but this task
has not run its complete verifier or certified its evolving closure. It is
therefore **UNVERIFIED IN-PROGRESS**, not another completed tier. No apparent
absence of `sorry` or green component build is counted as completion. A future
completion would still need its exact semantic scope distinguished from the
rare-prior Psi theorem and a general iid latent-reservoir realization.

## Current-run replay

Command: `python research/2026-10-27-minimax-audit/formal/replay.py`.
The script uses the pinned local Lean toolchain, calls the unchanged original
lock/declaration/axiom validation functions, and builds all 51 involved modules
sequentially. It then elaborates a new audit source that checks 46 original
exact target types, every Tier 3 and Tier 4 target against its fixed statement,
the exact full 713 type, and both Route A bridge statement types. All registered
public roots receive transitive `#print axioms` checks; missing roots fail.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.

The initial invocation failed before launching Lean because Windows did not
resolve `lake` from a child-only PATH. The replay driver now names the same local
lake executable explicitly; no validator or mathematical source changed to
resolve this environment issue. The successful/pending status must be read from
the newly generated `formal/replay.json`; historical success JSON files are not
used as current evidence. The script records source hashes before builds and
requires them and all checked locks to remain unchanged afterward. Concurrent
Tier 5 edits affect its global-source flag even though those files are not
imported by any audited root; that original result will be preserved separately
from any subsequent audit of the exact imported dependency closure.

Actual result: all 51 cache-aware Lake module build invocations exited zero.
The fresh exact-type/axiom audit also exited zero and reported all 398 expected
roots, using exactly `propext`, `Classical.choice`, and `Quot.sound`. This was
not a cold rebuild of all Mathlib dependencies. The broad replay nevertheless
correctly reports `valid=false`, because five concurrent Tier 5 files changed
during it. All original checked locks stayed unchanged. That failed global
stability checkpoint is preserved in `formal/replay.json`, without adjustment.

A separate command, `python research/2026-10-27-minimax-audit/formal/scoped_recheck.py`,
then checked the exact local import closure of the same audit against the
pre-build source hashes, verified all original locks again, and freshly
elaborated the identical exact-type/axiom source. It passed with exit zero,
**398/398 roots**, no disallowed axiom, and unchanged imported sources and locks.
The five edited Tier 5 files are explicitly listed as outside this closure;
none is imported by the accepted roots. This new checkpoint is
`formal/scoped_recheck.json` and its full output is `formal/scoped_recheck.log`.
It is a current-source replay of the listed statements, not certification of
the entire concurrently changing checkout. No old validator was weakened.

The dependency/axiom audit used Lean 4.36.0-rc1, commit
`c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`, and the frozen Mathlib manifest
revision `9bdd0bc71aaae0fd83889f9aacd70c32fccd1bcd`. The scoped recheck observed
HEAD `c11aa9ba41eb30beb040b979b074a0629fe79e1e`; source hashes, rather than the
initial commit name alone, identify what was checked. Counts are 46 original
exact targets, 152 Tier 3 roots including 11 exact-type roots, 65 Tier 4 roots
including six exact-type roots, 130 registered full-713 roots, and five inherited
Route A roots. The exact full-713 and two Route A statement types were also
elaborated. Every counted target is proved; no incomplete target is accepted.

## Correct scope for the unfinished countable bridge

The existing stop-under-both theorem cannot be copied with `Fin m` replaced by
an unbounded reservoir. The counterexample in `formal/stopping_bridge.tex`
pinpoints why. A new specification should build one iid reservoir process,
prove canonical first-observation numbering and consistent finite-prefix laws,
and require admissibility under every minimax alternative. Finite-prefix
information then gives terminal testing by the paper limiting lemma without
transferring termination across infinite product measures.

The new `formal/MODEL_EXTENSION_SPEC.md` and its separate immutable v1 hash lock
record paper targets only. They are not mislabelled as an accepted Lean
specification or a kernel proof. No new trivial Lean target was added to inflate
coverage. A complete reservoir construction, rare-prior information theorem,
and critical upper algorithm remain substantive formal obligations.
