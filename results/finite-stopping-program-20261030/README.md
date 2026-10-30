# Exact finite-law stopping program

This additive checkpoint follows `70f5573` on the branch based at `8fc36ac`.
`status.json` records the exact identities of 103 protected sources;
`ExactAudit.lean` preserves the independently stated targets.

For every finitely supported probability gap law and positive rarity bound,
Lean proves equivalence of the original robust certificate feasibility with
four finite cutoff/excess systems, together with the unchanged flow cone and
nonnegative bias and variance. The reduction retains both bias signs, the
variance constraint, and the work constraint. It rewrites all baseline
integrals as finite weighted sums. Zero weights and repeated support points
are allowed. Each excess variable is nonnegative and at least the signed
polynomial value minus its cutoff; all resulting excess constraints are linear.
The cone's quadratic perspectives are unchanged.

The underlying robust reduction holds for arbitrary probability laws: the
four universal prior constraints are equivalent to four scalar rarity cutoffs.
This uses the proved fractional support theorem and actual count-likelihood
polynomials, with no assumed finite reduction or compactness premise.

The audit rebuilt the two new modules, checked 119 declarations across
17 stopping-program modules, two exact types, and all transitive axioms.
Only `Classical.choice`, `Quot.sound`, and `propext` occur. Other dependencies
used cached objects with recorded source identities. All four verifier
regression tests passed. This is local verification, not a CI claim or a
complete dependency rebuild.

Reproduce with `python tools/verify_finite_stopping_program.py --cached-dependencies`;
omit the flag for a full local-dependency rebuild. Fresh runs belong in `.runtime`.
Logs `001.log` and `002.log` are module builds; `003.log` is the exact-type and
axiom audit. Statistical flow realization, the factor-sixteen risk comparison,
and genie convergence remain separate work.
