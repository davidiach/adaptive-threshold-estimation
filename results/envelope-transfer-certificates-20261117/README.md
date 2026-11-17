# Envelope and transfer certificate verification record

Clean source checkpoint: `62a035a3b5d6edc84a35846c3f8686cf3e88b2db`. Base main: `378912ab1999e8260a080b1ab0e96cf79e4dc199`
(#123, reviewed and merged after all 16 checks passed at `bd021617f600a3f26cc7fee35299b7a5b79c1334`).
This is local verification evidence, not a CI result for the new checkpoint.

## Evidence identity

The focused audit ran from the clean source checkpoint above. `status.json`
retains that commit and empty worktree status. The 116-file locked mathematical
and toolchain dependency closure and all 146 input hashes bind the
checked statements and actual-output proofs to this commit. Publication checks
every source and artifact checksum again. The whole-project build/add-only audit
ran before that commit; its unchanged Lean sources and resulting definition lock
are bound by `project-status.json`. The complete report validates against the
committed registry and all old fingerprints. This distinction is explicit;
no earlier run is relabeled as a clean-checkpoint audit.

## Checked scope

- Twelve exact statement types and all 22 declaration-root transitive axiom reports.
- Independent kernel replay of all three new envelope/rounding/transfer modules.
- Sixteen closed proofs about actual toolkit outputs: all-zero and flat envelopes,
  fallback at and above rarity, normalized residual-zero and positive-only splits,
  fractional quantile boundaries, exact resolution thresholds, null-prefix
  integrals and both work branches; single and multiple rounding bands, endpoint
  gaps and merged destinations; zero/nonzero TV radii, capped transfer endpoints
  and explicit original-K enclosure premises.
- Fifteen false outputs rejected by numerical contradictions in Lean: fallback
  placeholders, prefix, conditional rarity, core fractions, band costs, unresolved
  mass, inverse cost, error/work, rounding factor and grouped mass, transfer
  endpoints, downward transport and a transport crossing a band boundary.
- 1,263 modules built; 13,890 constants and
  11,165 theorems audited, plus 137 exported instances.
  All 2,589 old definition fingerprints preserved; 8 added
  by the official add-only tool, for 2,597 total.
- All 319 toolkit tests and six focused audit guards passed.

`audit.lean` independently restates the types; `audit.log` reports every root.
`sample-*.json/.lean/.log` preserve actual outputs and checked closed proofs.
`rejected-*.lean/.log` are intentionally failing numerical checks, not theorems.
`status.json` binds the source snapshot, compiler and kernel-checker binaries and
focused artifacts; `project-status.json` binds all project sources to its audit.
`SHA256SUMS` covers every record file except itself. Reproduce with
`python tools/verify_envelope_transfer_certificates.py`.

## Boundaries

Fallback callback zeros are placeholders, not error/work integrals. True-law
CDF domination requires valid population CDF bounds. Transfer requires an actual
input enclosure of original K, the TV bound and measurable band-preserving
rounding premises; a feasible-objective lower endpoint does not supply this.
The rounding theorem checks the returned transport contract and pushforward;
it is not a universal refinement of the Python ceiling-grid algorithm.
The null-prefix mixture identity does not verify physical zero-gap coin execution.

Global menus/DP/approximation outputs, planner prices and allocations, schedules,
floating arithmetic, CPython and stochastic/PRNG execution remain outside this
milestone. Input/source/process binding and the imported compiled cache remain
trusted. No universal producer-completeness or polynomial bit-cost claim is added.
#85 remains open; the core theorem/publication is unchanged.

CI now uploads both `.runtime/finite-law-certificates/` (omitted from #123's
artifact paths despite successful audit steps) and `.runtime/envelope-transfer-certificates/`.
This record makes no claim that #123's archive contained the finite-law status.
See the [contract and limits](../../docs/ENVELOPE_TRANSFER_CERTIFICATES.md).
