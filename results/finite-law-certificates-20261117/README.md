# Finite-law certificate verification record

Source checkpoint: `8243b72bd4b22beea396bc3f0e8b2d2f92986b06`. Base main: `e677e3ff496cdd0c08111e6843b99b6a754134de`
(#122, reviewed and merged after all 16 checks passed at `62f86c8045d77b249b10eebb92dabf4a963401a7`).
This record is local verification evidence, not a CI result for the new checkpoint.

## Evidence identity

The focused audit ran while the new files were uncommitted, atop
`62f86c8045d77b249b10eebb92dabf4a963401a7`. Its original `status.json` retains that base and
worktree status; it has not been relabeled as a clean-checkpoint run.
Before publication from the clean source checkpoint above, the publisher checked
that every audited input byte and every output checksum still matched. The
69-file locked mathematical dependency closure and the full input snapshot bind
the checked statements and actual-output proofs to this commit. `checkpoint.json`
records this mapping explicitly. No proof or adapter source changed after the run.

## Checked scope

- Ten exact statement types and all 52 declaration-root transitive axiom reports.
- Independent kernel replay of all five new finite-law modules.
- Finite atomic probability/integration, exact dyadic costs and original entropy,
  fractional quantile cores, and the original capped feasible selection objective.
- Eight closed proofs about actual toolkit outputs: empty/full/fractional
  selections, endpoint and mixed null-prefix laws, fractional/exact quantile
  boundaries, threshold equality and both tail-work branches.
- Eight tampered outputs rejected by numerical contradictions in Lean: objective,
  prefix, core fractions, band costs, unresolved mass, inverse cost, error and work.
- 1,260 project modules built; 13,843 constants and
  11,126 theorems audited, plus 137 exported instances.
  All 2,575 old definition fingerprints preserved; 14 added
  by the official add-only tool, for 2,589 total.
- All 307 toolkit tests and six focused audit guard tests passed.

`audit.lean` restates the exact contracts; `audit.log` reports every root.
`sample-*.json/.lean/.log` preserve actual output certificates and checked proofs.
`rejected-*.lean/.log` are intentionally failing numerical checks, not theorems.
`status.json` binds the source snapshot, compiler and kernel-checker binaries and
all focused artifacts. `project-status.json` binds every project source and the
unchanged whole-project audit to its report. `SHA256SUMS` covers every record file
except itself. Reproduce with `python tools/verify_finite_law_certificates.py`.

The objective interval encloses one capped feasible objective; only its upper
endpoint is a certified bound on original K. Global optimization is not proved.
Finite oracle certificates apply at the requested cap. Zero-gap envelope laws,
arbitrary callback promises, transfer/rounding outputs, global DP/approximation,
planner prices and schedules, floating arithmetic, CPython semantics and stochastic
execution remain outside this milestone. Input/source/process binding and the
imported external compiled cache remain trusted. No universal producer-completeness
or polynomial bit-complexity claim is added. #85 remains open.

See the [contract and limits](../../docs/FINITE_LAW_CERTIFICATES.md).
