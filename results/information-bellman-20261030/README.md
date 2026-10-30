# Actual information-ratio Bellman characterization

This additive checkpoint follows `b41c950` on the branch based at `8fc36ac`.
Exact identities of 108 protected sources are in `status.json`.
`ExactAudit.lean` preserves five independently stated targets.

For every probability gap law, four-prior tuple and positive cap, the actual
normalized count-flow information/work ratio has the following characterization.
It is infinite exactly when a valid prefix has zero variance-reference mass
and nonzero endpoint contrast. Otherwise a deterministic count stopping rule
attains it. The Bellman price function is continuous and strictly decreasing,
and its unique zero is the ratio. Root activation is charged and the rule
stops at the cap. The price function is also the existing finite maximum of
affine tree scores, so its finite representation is exact.

The proof constructs cone flows from count policies, proves complementarity
for the Bellman decisions, and matches actual count information to prefix
rewards. It also proves that prefix information increments are nonnegative
and that their sum against continuation weights equals terminal information.
Null references use the closed perspective; they are not discarded.

The audit rebuilt seven new modules, checked 189 declarations in 22 modules,
five exact types, and all transitive axioms. Only `Classical.choice`,
`Quot.sound`, and `propext` occur. Other dependencies used cached objects with
recorded source hashes; this was not a full dependency rebuild or a CI run.
All four verifier regression tests passed.

Reproduce with `python tools/verify_information_bellman.py --cached-dependencies`;
omit the flag for a full local-dependency rebuild. Fresh runs belong in `.runtime`.
The first seven logs are source builds; `008.log` is the exact-type/axiom audit.

The statement here uses the actual count-flow cone. The remaining connection
from arbitrary seeded ordered stopping procedures to these flows, adaptive
testing transfer, factor-sixteen certificate and genie convergence are separate
work. The entropy-tail statistical lower bound remains with the cloud session.
