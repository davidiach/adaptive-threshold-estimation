# Published verification evidence

These files record particular source checkpoints and experiments. Use
[docs/RESULTS.md](../docs/RESULTS.md) for current claim scope and
[docs/VERIFY.md](../docs/VERIFY.md) to reproduce a check. A stored pass applies to
the sources and targets it audited; it does not establish that a later checkout
or CI run passes. A record's source hashes describe its own checkpoint, so they
can differ from the current files after a later proof-only change: the
[hard-budget record](hard-budget-rms-20261104/README.md), for example, lists
eight Lean files that were refactored afterwards without changing a
statement. For the current tree the evidence is the CI run on that commit.

## Records referenced by the current guides

| Claim or check | Published record |
|---|---|
| Entropy perturbation and certified-bin state-compression invariant | [selection-approximation-20261106](selection-approximation-20261106/README.md) |
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
| Arbitrary-law $\Psi$ lower bound through the entropy-tail law | [psi-selection-20261109](psi-selection-20261109/README.md) |
| Whole-project build, axiom audit and main-theorem kernel replay | [project-axioms-20261109](project-axioms-20261109/README.md) |
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
a disposable checkout containing the change being checked. The later theorem
audits that save logs write them under `.runtime/`; audits added from
4 November onward only print their kernel report. The [tool index](../tools/README.md) describes the
other temporary output locations. Keep local reruns out of the published records.

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
exact saving comparison and interval certificates. The
[new 13-statement connection](gap-law-menus-20261105/README.md) additionally
constructs the actual finite-law menus and proves their compressed optimum
equals the original $K$, including atomic cost and saving formulas.
Python execution remains unverified.

## Ordinary cap truncation

The [native ten-statement audit](finite-cap-truncation-20261105/README.md)
verifies a uniform square-root rate for the ordinary optimized cap program,
its output-preserving certificate construction, and the explicit risk bound.
Optimality and the corresponding genie rate remain open.

The [finite-family adaptation component audit](law-adaptation-20261105/README.md)
checks 17 exact types, including observable parity, bounded-average concentration,
identification, selected-event transfer and the delayed oracle-rate comparison.
The [22-statement realization audit](law-adaptation-realization-20261105/README.md)
adds moment determinacy and the complete observable finite-family controller,
with actual flip accounting, nested compatible intervals and joint all-budget
coverage and oracle width. Arbitrary-law adaptation has a
[paper proof](../docs/ARBITRARY_LAW_ADAPTATION.md); Lean checks components of it only.

The [finite arbitrary-law entropy transport audit](arbitrary-law-entropy-20261106/README.md)
adds 15 exact statements, including the geometric factor-three comparison.
It does not yet establish the full arbitrary-law adaptation theorem.

The [finite CDF-envelope audit](arbitrary-law-envelope-20261106/README.md)
adds 25 exact statements and 24 axiom reports for the conservative finite
measure, its zero atom and CDF domination from finite grid bounds.

The [observable learned-law stage audit](arbitrary-law-stage-20261106/README.md)
adds 17 exact statements and 16 axiom reports: a valid learned probability
law on every word, fresh continuation labels, physical caps, history readback,
and the original-experiment joint endpoint law. Statistical instantiation
and the full all-budget controller remain outside this component.

The [countable entropy-transport audit](arbitrary-law-countable-20261106/README.md)
adds 16 exact statements and axiom reports. It extends the factor-three bound
to countably many locally summable destination columns, allows infinite total
cost and entropy, and identifies the result with canonical Gamma for finite
gap measures with a supplied band-cell decomposition.

The [increasing-gap coupling and selection audit](arbitrary-law-coupling-20261106/README.md)
adds 32 exact statements and transitive reports. It constructs canonical
band cells from a finite increasing coupling on positive gaps, lifts every
fractional selection, preserves mass and domination, and proves the original
selection comparison with coefficient sqrt(3), allowing infinite moments
and entropy. CDF coupling existence and the zero-atom extension remain separate
at that checkpoint.

The [CDF coupling and zero-atom audit](arbitrary-law-zero-cdf-20261106/README.md)
adds 47 exact statements and transitive reports. It constructs the common-
uniform increasing coupling from CDF domination, extends the entropy-tail
functional to unresolved mass at zero, proves exact agreement with positive-
gap K, and derives the sqrt(3) comparison from CDF domination on `[0,1/2]`.

The [dominated-mass audit](arbitrary-law-dominated-20261106/README.md)
adds 22 exact statements and transitive reports for bounded density
restriction, entropy and tail algebra, residual control, and comparison (A5)
for finite measures, allowing infinite entropy and preserving the cap.

The [concrete light-contraction audit](arbitrary-law-light-20261106/README.md)
adds 62 exact statements and transitive reports. It constructs the multiplier
from a uniform variable, proves its exact CDF, derives product-law entropy
and residual-tail bounds, and proves the full factor-32 selection comparison.

The [sign-neutral tail-test audit](arbitrary-law-tail-test-20261110/README.md)
adds 91 exact statements and transitive reports for the single-coin test of
the tail certificate: its work cap, flip symmetry and sign-neutral law, both
unresolved-probability bounds, the multiplier comparison and the expected-work
bound. Inverse sampling and the pilot are not part of it.

The [capped tail-probe audit](arbitrary-law-tail-probe-20261110/README.md)
adds 69 exact statements and transitive reports for one probe of the tail
certificate's inverse-sampling step: its caps and charge, dependence on the
bought flips, coverage at every budget with probability at least 7/8, and the
fixed-budget performance bound with probability at least 3/4. The median over
probes, the oracle comparison and the pilot are not part of it.

The [tail-median audit](arbitrary-law-tail-median-20261111/README.md) adds 51
exact statements and transitive reports for the median over independent
probes: the majority transfer to the median, Hoeffding across probes,
statement (1) of the tail certificate with its pathwise flip cap, the
statement at every depth at once, and both on a single coin array. The oracle
comparison and the pilot are not part of it.

The [tail-oracle audit](arbitrary-law-tail-oracle-20261111/README.md) adds 26
exact statements and transitive reports for the oracle comparison of the tail
certificate: the kernel bounds, the split of the gap law at its quantile, the
onset condition and its existence, and the bound of the median by 524288 times
the selection functional. The pilot is not part of it.

The [tail-observable audit](arbitrary-law-tail-observable-20261111/README.md)
adds 68 exact statements and transitive reports for the tail certificate in
the observable experiment: a reader that runs the probes from observed flips,
the certificate as a function of the observed word, the transfer of events
about that word to the law of the original experiment, and statements (1) and
(3) for the estimator's output with coverage at every pause. The estimator
buys every block in full. The pilot is not part of it.

The [pilot audit](arbitrary-law-pilot-20261111/README.md) adds 66 exact
statements and transitive reports for the capped multi-depth pilot of the
adaptation proof: its budgets and caps, the event (A8) at every depth at once
with a common number of probes, the pilot installed in the paid learning
stage, and the learned law (A9), which dominates the gap law on that event.
The learned law's comparison with the oracle is not part of it.

The [pilot-onset audit](arbitrary-law-pilot-onset-20261111/README.md) adds 25
exact statements and transitive reports for the first part of that
comparison: the lowest-gap split of the gap law, the pilot's work estimates
(A12), its onset, and the bounds of the work and of the coin cap by the
selection functional. The learned-CDF bound and the final comparison are not
part of it.

The [learned-oracle audit](arbitrary-law-learned-oracle-20261111/README.md)
adds 31 exact statements and transitive reports for the rest of that
comparison: the learned-CDF bound (A13), the slack bound (A14), the
clipped-CDF witness, and the comparison (A11) of the learned law with the
oracle, with factor $2^{24}$ past a finite onset, on the pilot event. The
robust continuation is not part of it.

The [zero-quantile audit](arbitrary-law-zero-quantile-20261112/README.md) adds
22 exact statements and transitive reports for (A16): the quantile design of
a law with mass at zero, the comparison $Q_\alpha\le4K_\alpha$ with the
selection functional, and the converse. The planner that uses the design is
not part of it.

The [known-law planner audit](known-law-planner-20261112/README.md) adds 49
exact statements and transitive reports for the plan of the known-law
estimator: its level races and level price, its cap search, its counts, and
the validity of its squared-error certificate for every admissible plan. The
price is that of the checked upper theorem. The plan's rate and the toolkit's
own price are not part of it.

The [plan-rate audit](known-law-plan-rate-20261112/README.md) adds 18 exact
statements and transitive reports for the rate of that plan with the exact
integrals of the quantile split: the smaller of $\rho/2$ and its certified
risk is at most $(1+\tfrac85\max\{2048,28000\sqrt\theta\})$ times the
selection functional, and its reported radius at most six times that. The
rate of a plan computed from upper bounds is not part of it.

The [tight-rate audit](known-law-plan-tight-rate-20261112/README.md) adds 31
exact statements and transitive reports for the rate of that plan computed
from upper bounds within a factor two, for a law of positive gaps and for a
reference law with mass at zero. For dyadic weights the smaller of $\rho/2$
and the certified risk of the latter is at most $C_0K_\alpha$ with
$C_0=1+4\max\{4096,8\sqrt2\cdot28000\}$, and the reported radius at most
$6C_0K_\alpha$. These are statements about the plan's certificate; an
experiment with coins of gap zero is not part of it.

The [planner-output audit](known-law-planner-output-20261112/README.md) adds
9 exact statements and transitive reports for the planner end to end: the
quantile split is constructed for every law of positive gaps, and the
planner's output gives minimax risk at most $44801$ times the selection
functional with exact integrals, and the factor-two coefficient for every
tight enclosure.

The [robust-error audit](robust-error-transfer-20261113/README.md) adds 33
exact statements and transitive reports for the first part of the robust
continuation: the raced classifier is monotone in the flips, its error on
one coin does not increase with the gap, and its population error under a
true law coupled above the reference is at most the reference bound plus
the uncoupled mass. The coupling is a hypothesis, and the work of the race
is not part of it.

The [robust-work audit](robust-coin-work-20261113/README.md) adds 9 exact
statements and transitive reports for the work of the race on one coin: the
ordinary, negative-bank and positive-bank bounds of the known-law theorem
hold at a reference gap for a coin of every larger gap. The level work
under a coupling is not part of it.

The [robust-level audit](robust-level-certificates-20261113/README.md) adds
18 exact statements and transitive reports for the two certificates of a
level race under a true law coupled above its reference: its expected work
is at most the level-work certificate of the known-law theorem with the
uncoupled mass added to the unresolved mass, and its error at most
$\delta_l$. The bank's null law is the positive part of the reference, so a
reference with mass at zero needs no coin of gap zero. The coupling in that
form is a hypothesis, and the corrections and the plan under the true law
are not part of it.

The [robust-plan audit](robust-plan-20261114/README.md) adds 20 exact
statements and transitive reports for the plan of a reference law under the
true law. An admissible plan spends at most the budget and has
root-mean-square risk at most the square root of its certificate, and one
estimator, fixed by the reference $\alpha$, has risk at most $C_0K_\alpha$
under every true law coupled above $\alpha$. The coupling is a hypothesis;
the capped median and the connection to the paid stage are not part of it.
