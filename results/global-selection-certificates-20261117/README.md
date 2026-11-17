# Global selection certificate verification record

Clean source checkpoint: `997b6f1f1ce65a39e566063885d4b8fc09de25b1`. Base main:
`8d79c516d6f20484d27a220003e06e593018675a` (#124, reviewed and merged after all 16 checks passed
on `aa0071bf5d448009d387fb5174c99494422cdd05`). This record is local
verification evidence, not a CI result for the new checkpoint.

## Evidence identity

The focused audit ran from the clean source checkpoint above. `status.json`
retains that commit and empty worktree status. The 75-file locked mathematical
and toolchain dependency closure and all 106 audit-input hashes bind
the universal statements and actual-output proofs to this source. Publication
rechecks every source and artifact checksum. The whole-project audit ran before
the source commit; `project-status.json` maps its unchanged Lean sources and
resulting definition lock to this checkpoint. Existing compiled project objects
were reused after building the two new modules and their dependency closure.
This record does not claim a fresh local rebuild of all project modules.

## Checked scope

- Eleven exact statement types and all 24 declaration-root axiom reports.
- Independent kernel replay of both new modules.
- Eleven closed proofs about actual exhaustive, DP and approximation outputs:
  one-atom exact and saturated branches, a same-band menu with three suffixes,
  multiple bands with a proper selected subset, exact optimizer flags, actual
  witness intervals, relative guarantees, and saturation with a returned DP
  witness. Exhaustive saturation preserves the missing legacy witness.
- Eleven rejected certificates: false global lower/upper bounds, wrong witness,
  wrong epsilon or witness interval, incomplete/duplicate menu, wrong suffix
  count, a false optimizer claim, a failed relative stopping inequality, and a
  nonsuffix witness whose capped objective alone would satisfy the interval.
- Whole-project audit of 13,941 constants and 11,192
  theorems across 1,265 modules, plus 138 exported instances.
  All 2,597 prior definition fingerprints are preserved; 24 new
  entries were added by the official tool, for 2,621 total.
- All 329 toolkit tests and six focused audit-guard tests passed.

The only allowed transitive axioms are `propext`, `Classical.choice`, and
`Quot.sound`. `audit.lean` independently restates the exact types; `audit.log`
reports every root. `sample-*.json/.lean/.log` preserve actual producer-output
projections and their closed proofs. `rejected-*.lean/.log` are deliberately
failing obligations, not theorems. `status.json` binds the source snapshot,
compiler and independent kernel checker and every focused artifact.
`SHA256SUMS` covers every published file except itself. Artifact hashes cover
exact saved bytes. The adapter's `proof_sha256` covers generated UTF-8 text with
LF newlines; Windows text-mode file writes save CRLF. These 11 source hashes
were therefore independently checked after text-mode newline normalization,
while every artifact checksum was checked without normalization. Reproduce with
`python tools/verify_global_selection_certificates.py`.

## Boundaries

The certified global interval is for the original all-submeasure optimization
problem. It is not statistical risk. The output checker uses complete suffix
menus even for DP/approximation results, with at most six atoms and 64 suffixes.
Some valid outputs can fail when the proof generator cannot separate ties or
meet its source, precision or time limits. No universal producer-completeness,
polynomial verification-cost or bit-complexity claim is made.

Generic pruning and rational-bin primitives are checked, but this adapter does
not certify full internal solver traces, rounded-log parameter construction,
state/transition counters or precision-refinement history. Those are outside its
output projection. Other selection entry points, concrete planners/schedules
and floating calculators remain in #85. Input/source/process binding and the
imported compiled cache remain trusted; CPython and PRNG refinement remain #86.
All prior frozen sources and evidence are unchanged.

CI runs this audit and its guards and uploads `.runtime/global-selection-certificates/`.
Its kernel job has a 90-minute timeout to accommodate the additional audit.
See the [contract and limits](../../docs/GLOBAL_SELECTION_CERTIFICATES.md).
