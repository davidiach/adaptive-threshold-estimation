# Published verification evidence

These files record particular source checkpoints and experiments. Use
[docs/RESULTS.md](../docs/RESULTS.md) for current claim scope and
[docs/VERIFY.md](../docs/VERIFY.md) to reproduce a check. A stored pass applies to
the sources and targets it audited; it does not establish that a later checkout
or CI run passes.

## Records referenced by the current guides

| Claim or check | Published record |
|---|---|
| Original frozen Lean target audit | [lean_checkpoint.json](lean_checkpoint.json), [lean_score.json](lean_score.json) |
| Uniform713 and information milestones | [uniform713_status.json](uniform713_status.json), [tier3_status.json](tier3_status.json), [tier4_status.json](tier4_status.json), [tier5_status.json](tier5_status.json) |
| Main RMS lower bound | [tier6_status.json](tier6_status.json) |
| Distribution-blind RMS upper bound | [blind_upper_components_002.json](blind_upper_components_002.json) |
| Full critical quadratic lower bound | [critical_components_016.json](critical_components_016.json) |
| Full critical quadratic upper bound | [critical_upper_components_003.json](critical_upper_components_003.json) |
| Critical Psi formula and minimax separation | [critical_psi_001.json](critical_psi_001.json) |
| All-size entropy and explicit single-coin costs | [critical_all_sizes_002.json](critical_all_sizes_002.json) |
| Observable unbiased converse | [unbiased_converse_001.json](unbiased_converse_001.json) |
| Observable 713 and unbiased existence characterization | [observable713_001.json](observable713_001.json) |
| Confidence characterization | [confidence_001.json](confidence_001.json) |
| Magnitude-oracle lower bounds | [oracle_lower_001.json](oracle_lower_001.json) |
| Observable rare-event rate above alpha two | [rare_above_two_001.json](rare_above_two_001.json) |
| Rare-event upper bounds, quantile comparison, stopping program, identification and genie certificates (full rebuild; see the note below) | [rare-event-full-20261031](rare-event-full-20261031/README.md) |
| Complete entropy-tail lower and two-sided law (cached dependencies; source and artifact hashes recorded) | [entropy-tail-complete-20261101](entropy-tail-complete-20261101/README.md) |
| Explicit arbitrary-law entropy-tail and quantile lower bounds | [entropy-tail-explicit-20261104](entropy-tail-explicit-20261104/README.md) |
| Finite-law bandwise-suffix optimizer and sufficient search family | [bandwise-suffix-20261104](bandwise-suffix-20261104/README.md) |
| Total variation, rounding, transported enclosures and finite approximation | [selection-stability-20261104](selection-stability-20261104/README.md) |
| Quarter smoothing in both KL directions | [quarter-smoothing-20261104](quarter-smoothing-20261104/README.md) |
| Generic RMS obstruction transfer and additive submeasure localization with coefficient $1/128$ | [rms-localization-20261105](rms-localization-20261105/README.md) |
| General-law confidence coefficients $10^{-17}$ and $750000$ | [entropy-confidence-20261105](entropy-confidence-20261105/README.md) |
| Fractional-submeasure additive confidence localization with coefficient $1/128$ | [additive-confidence-20261105](additive-confidence-20261105/README.md) |
| Common pairs from variance–null-work obstructions and the $1/128$ confidence consequence | [common-pair-20261105](common-pair-20261105/README.md) |
| Selected-type information transfer through unbounded stopping | [adaptive-types-20261105](adaptive-types-20261105/README.md) |
| Fresh-state upper-bound transfer and complete observed-state rates | [observed-state-upper-20261105](observed-state-upper-20261105/README.md) |
| Continuous-magnitude observed-state lower bounds and regularity | [continuous-observed-lower-20261105](continuous-observed-lower-20261105/README.md) |
| Finite-cell observed-state lower bound | [finite-observed-20261105](finite-observed-20261105/README.md) |
| Smooth-density complexity and unbiased impossibility | [smooth-density-20261105](smooth-density-20261105/README.md) |
| Prior-family and per-flip information inequalities for the all-law time-uniform lower bound (the complete theorem is a paper proof) | [anytime-lower-20261105](anytime-lower-20261105/README.md) |
| Observable time-uniform confidence for known laws | [anytime-confidence-20261105](anytime-confidence-20261105/README.md) |
| Logarithmic and intermediate rare power margins | [shifted-power-20261105](shifted-power-20261105/README.md) |
| Rare power margins below exponent one | [sublinear-power-20261105](sublinear-power-20261105/README.md) |
| Unknown laws under a stochastic envelope | [stochastic-envelope-20261105](stochastic-envelope-20261105/README.md) |
| Fixed confidence at the effective budget for every known law | [known-law-confidence-20261104](known-law-confidence-20261104/README.md) |
| Hard-budget fallback and three RMS minimax bounds | [hard-budget-rms-20261104](hard-budget-rms-20261104/README.md) |
| Critical-law minimax confidence lower bound | [critical-confidence-20261104](critical-confidence-20261104/README.md) |
| Uniform finite-cap convergence and the linear sufficient cap | [genie-rate-20261104](genie-rate-20261104/README.md) |
| Exact scalar-root quantile factor and finite-law sharpness | [quantile-optimality-20261105](quantile-optimality-20261105/README.md) |
| All-law quantile upper comparison at the exact scalar-root factor | [sharp-quantile-upper-20261105](sharp-quantile-upper-20261105/README.md) |
| Sharp finite-core selection reduction and entropy Lipschitz bound | [quantile-core-reduction-20261105](quantile-core-reduction-20261105/README.md) |
| Sharp finite-vector quantile factor and unique scalar root | [optimal-quantile-root-20261105](optimal-quantile-root-20261105/README.md) |
| General-law $31/20$ quantile comparison | [quantile-price-20261104](quantile-price-20261104/README.md) |
| Single-type population confidence transfer and common-pair lower bound | [confidence-population-20261104](confidence-population-20261104/README.md) |
| Eight-fifths quantile-selection comparison for arbitrary laws | [quantile-selection-20261104](quantile-selection-20261104/README.md) |
| Direct finite-law quantile bounds and estimator quantifiers | [direct-finite-quantile-20261104](direct-finite-quantile-20261104/README.md) |
| Universal closed-quantile minimax corollary (cached dependencies) | [closed-quantile-law-20261101](closed-quantile-law-20261101/README.md) |
| Constant search and scope | [constants_theory.json](constants_theory.json), [constants_finite_grid.json](constants_finite_grid.json), [process account](../docs/process/TRACK_B.md) |
| Real-valued benchmark | [real_comparison.json](real_comparison.json), [real_verification.json](real_verification.json), [benchmark protocol](../benchmark/README.md) |

The `rare-event-full-20261031` record was produced by a parallel integration
of #33, on branch `feat/rare-event-verified-integration-20261030` (commit
`fc099bb`), and is imported here unchanged. It certifies that branch's proof
commit `2036bd1`: a rebuild of all 518 local dependency modules and an
exact-type and transitive-axiom audit of 1,789 declarations. Of the 263
modules imported from #33, 262 are byte-identical in `main`. The other,
`Genie/AtomConicModel.lean`, differs only by a removed trailing space. The
record audited that branch's own bridge to the frozen interface
(`EntropyTailBridge/`), not `main`'s
[`EntropyTail/Bridge.lean`](../lean/ThresholdHC/EntropyTail/Bridge.lean) and
[`Upper.lean`](../lean/ThresholdHC/EntropyTail/Upper.lean). `main`'s bridge is
checked by `verify_entropy_tail.py` in the `entropy-tail-upper` CI job. The
record's reproduction tool, `tools/verify_rare_event_completion.py`, exists
only on that branch.

Rare-event manuscript evidence lives beside that publication, in its
[build record](../paper/rare-event/v2/VERIFICATION.json) and
[audit index](../paper/rare-event/audit/README.md). The finite-gap manuscript
keeps its file hashes and check scope in its own
[SHA256SUMS](../paper/finite-gap-rare-events/SHA256SUMS) and
[provenance note](../paper/finite-gap-rare-events/PROVENANCE.md). Sealed research checkpoints
remain with their [research packages](../research/README.md).

## Interpret a record

Check its source identity, target list, scope, and completion fields together.
Numbered records preserve successive audits; a higher number is not a stronger
theorem by itself. For example, a critical lower-only audit can retain
`full_critical_minimax_theorem_verified=false` while a separate upper audit
completes the characterization. Read the
[critical audit explanation](../docs/CRITICAL_AUDIT.md#current-formal-boundary).

Files containing `baseline`, `attempt`, `draft`, `foundations`, or earlier
checkpoint numbers preserve the development history. Logs record build and
diagnostic details; numerical tables support only the experiments they describe.
Do not infer universal mathematical claims from a numerical score or infer
current CI status from a historical log.

## Fresh runs and publication

Several baseline and tier verifiers overwrite tracked files here. Run those in
a disposable checkout containing the change being checked. Later theorem audits
write under `.runtime/`; the [tool index](../tools/README.md) describes the other
temporary output locations. Keep local reruns out of the published records.

When a task calls for publishing new evidence, add a separately identified
record with its source identity, commands, outcome, and precise scope. Preserve
the prior records and update this index and the current claim guide as needed.
Never rename, overwrite, or rehash a historical artifact to make it describe
newer work.

The [observable sequential-testing audit](anytime-sequential-20261105/README.md) checks eight exact statements, including first-crossing summability and infinitely many width violations in the original adaptive experiment.

The [infinite-moment tail-family audit](anytime-tail-20261105/README.md) checks fifteen exact statements through the adaptive observable information transfer and an explicit unbounded integer-budget schedule.

The [complete time-uniform lower-bound audit](anytime-asymptotic-20261105/README.md) checks fourteen exact statements, including the all-law asymptotic comparison and observable interval consequence with coefficient $10^{-22}$.

## Finite-menu cost grouping

The [native 14-statement audit](band-cost-formal-20261105/README.md) verifies
the mathematical compression algorithm, state bounds, entropy price,
exact saving comparison and interval certificates. Its boundary excludes
the Python implementation and the concrete gap-law-to-menu construction.

## Ordinary cap truncation

The [native ten-statement audit](finite-cap-truncation-20261105/README.md)
verifies a uniform square-root rate for the ordinary optimized cap program,
its output-preserving certificate construction, and the explicit risk bound.
Optimality and the corresponding genie rate remain open.

The [finite-family adaptation component audit](law-adaptation-20261105/README.md)
checks 17 exact types, including observable parity, bounded-average concentration,
identification, selected-event transfer and the delayed oracle-rate comparison.
The full controller construction and moment determinacy remain paper proofs.
