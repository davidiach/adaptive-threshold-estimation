# Finite-law approximation and original-K certificate

The [proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/3a83256a1273e47bb137e1ac7dc3f04238feaa27)
proves `FiniteLawApproximationStatement` in the new
[specification](../../lean/ThresholdHC/FiniteSelectionApproximation/Specification.lean).
It covers every finitely supported probability law on `(0,1/2]`, including
rational finite laws, for `0 < rho <= 1/4`, `B > 0`, `0 < epsilon <= 1`.

For `beta=1+epsilon/4`, the retained bandwise suffix witness and rational
endpoints satisfy `0 < l` and

`l/beta <= K <= J(witness) <= u <= (1+epsilon)*l/beta`.

`K` is the original capped infimum over all fractional submeasures; `J`
evaluates the selected submeasure's original objective. The theorem derives
the concrete bin certificate, input parameters, zero-cost case, positive floor,
finite endpoint precision, every-stage state bound `S`, and at most `(n+m)S`
candidate extensions. The [scope guide](../../docs/FINITE_SELECTION_APPROXIMATION.md)
gives the formulas and the module map.

The [independent audit input](audit.lean) checks 12 exact statements, including
the full target with explicit constants and rational bin examples. The
[report](audit.log) gives all 93 transitive axiom reports using only `propext`,
`Classical.choice` and `Quot.sound`. The [Lake build](build.log) rebuilt the
current import closure. The [whole-project audit](project-audit.log) checked
13,412 constants, 10,868 theorems and 125 exported instances in 1,251 modules,
preserved all 2,402 existing definition fingerprints, and added 31 new ones.
Six new verifier guard tests, twelve whole-project guard tests and five source
guard tests passed; the source scan covered 1,252 Lean sources.

The successful local audit preceded the checkpoint commit. The preserved
[local metadata](local-status.json) records that execution honestly.
[status.json](status.json) binds every audited source byte to the proof commit,
including the 78-module project source closure, reused dependency hashes,
audit tools, compiler identity and toolchain files. Its new specification lock
pins 79 files. [SHA256SUMS](SHA256SUMS) identifies this evidence package.
These are local checks; CI on the actual PR head is a separate condition.

The mathematical logarithm/floor/ceiling and rational endpoint specifications
do not certify numerical-oracle or Python execution (#85). The polynomial
bit-complexity claim remains a paper proof with no formal machine cost model.
Exact polynomial-time selection (#87) remains open. The previous component
specification, research package, evidence and published PDFs are unchanged.

Run `python tools/verify_finite_selection_approximation.py` to create fresh
evidence. The `--no-build` used for this audit followed the successful current
build; it is not a substitute for building changed sources. Mathlib compiled
caches and the Lean distribution remain trusted inputs.
