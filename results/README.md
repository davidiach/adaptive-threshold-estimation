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
| Arbitrary-law deterministic quantile comparison | [entropy-tail-quantile-20261030](entropy-tail-quantile-20261030/README.md) |
| Observable entropy-tail and closed-quantile upper bounds | [entropy-tail-upper-20261030](entropy-tail-upper-20261030/README.md) |
| Fixed-cap identification and infinite-budget floor | [cap-identification-20261030](cap-identification-20261030/README.md) |
| Constant search and scope | [constants_theory.json](constants_theory.json), [constants_finite_grid.json](constants_finite_grid.json), [process account](../docs/process/TRACK_B.md) |
| Real-valued benchmark | [real_comparison.json](real_comparison.json), [real_verification.json](real_verification.json), [benchmark protocol](../benchmark/README.md) |

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
