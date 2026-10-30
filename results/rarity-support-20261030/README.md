# Rarity support and fractional cutoff

This additive checkpoint follows `475c2a7` on the branch based at `8fc36ac`.
The exact identities of 83 protected proof, tool and dependency sources are
recorded in `status.json`; `ExactAudit.lean` preserves the checked statements.

For every probability law on `(0,1/2]`, positive rarity bound, and measurable
L2 function bounded above almost everywhere by a nonnegative `M`, Lean proves
that the supremum of `integral q*f` over globally rare priors is attained.
It equals the minimum over `ell >= 0` of
`rho*ell + integral max(f-ell,0)`, with an attained cutoff in `[0,M]`.
An optimizer is explicitly `1` above the cutoff, one constant fraction in
`[0,1]` at the cutoff, and `0` below it. A positive cutoff saturates the rarity
budget. The proof includes null cutoff sets and atoms of positive mass.
Bounded measurable functions are covered by a separate corollary.

The audit rebuilt the six new modules and checked 41 declarations in nine
modules, two independently stated exact types, and all transitive axioms.
Only `Classical.choice`, `Quot.sound`, and `propext` occur. Dependencies used
cached objects with recorded source identities; this was not a complete
local-dependency rebuild or a CI run. All four verifier regression tests passed.

Reproduce with `python tools/verify_rarity_support.py --cached-dependencies`;
omit the flag to rebuild every local dependency. Fresh runs belong in
`.runtime`. The seven logs record six source builds and the final exact-type
and axiom check.

This is an optimization theorem. Statistical flow realization, the
factor-sixteen risk certificate, and genie convergence remain separate work.
The entropy-tail statistical lower bound remains assigned to the cloud session.
