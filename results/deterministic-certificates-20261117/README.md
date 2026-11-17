# Deterministic numerical certificate checkpoint

Proof, adapter and test checkpoint: `293d3864fe7b043aef565fc93d320bd4caa7e98f`.
Base main: `2e8e8b5e2a06a39f83db41376317f705789f9e0f`, after #119 and #121 merged.
This is local evidence from a clean committed tree. It is not a CI result for
this checkpoint or the later commit that publishes this record.

## Checked scope

- Eight exact statements and 39 complete transitive axiom reports.
- Independent kernel replay of all four new checker modules.
- Universal soundness for rational interval certificates, square-root precision,
  logarithm range reduction and the existing mathematical entropy definition.
- Eight closed kernel proofs about actual toolkit outputs, including tiny roots,
  an exact square, negative logarithms, default log precision and zero costs.
- Four numerical rejections reducing to `False`, including an over-wide root
  interval that encloses the value but fails its advertised precision.
- All 1,255 project modules built; 13,769 constants, 11,066 theorems and 137
  exported instances audited. All 2,575 definition fingerprints match; the
  official add-only operation preserved 2,433 old entries and added 142.
- All 297 toolkit tests and six new verifier guard tests passed on this checkpoint.

The final focused command was
`python tools/verify_deterministic_certificates.py --no-build --output-dir .runtime/det85-publication-audit`
after building the current sources. The final project command was
`python tools/verify_project_axioms.py --no-build`; all modules had been built
in Windows-safe batches. No existing Lean source, specification lock, sealed
research file or published evidence was changed.

## Artifacts and interpretation

`status.json` binds the 36 audit input files, compiler identity, kernel-checker
binary and every focused artifact. `audit.lean` independently restates the exact
types; `audit.log` reports every root. `sample-*.json`, `.lean` and `.log` expose
the actual output and its closed proof. `samples.json` summarizes the results.
The rejected sources and logs are intentionally unsuccessful numerical proofs;
they are not accepted theorems. `kernel-replay.log` records replayed modules.

`project-status.json` binds every project module, the definition lock and official
audit script to the final project report. Test logs are finite regression
evidence. `SHA256SUMS` covers every file in this record except itself.

## Boundaries

The producer is untrusted and acceptance is opt-in. CPython semantics,
serialization/process binding and the imported external compiled cache remain
trusted execution boundaries. No universal producer-completeness or polynomial
bit-complexity claim is made. Actual finite-law canonicalization, measure/oracle
identities, global selection, approximation transitions and planner/schedule
execution remain open in #85. Stochastic refinement remains #86.

See the [contract, API inventory and remaining work](../../docs/DETERMINISTIC_VERIFICATION.md).
The core theorem/publication and #89/#93 are already complete in their stated scopes.
