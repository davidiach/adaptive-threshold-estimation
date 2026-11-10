# CDF coupling and zero-atom selection: native Lean audit

Proof checkpoint: `5b2f8bd113126fb31d70a201a389c79e050b861d`.
Base checkpoint: `e69087b540a98824746bf371a7b19bd1dd02f8ef`, the published increasing-gap
coupling and selection checkpoint of PR #75.

The [record](status.json) binds all 62 project sources, 5 fresh
serial native compilations with empty logs, and 57 dependencies whose compiled
hashes match earlier published records. No inherited artifact is first
identified here. The pinned compiler, package manifests, audit tools and
prior evidence records are included in the hash bindings.

The new audits independently restate 47 exact statements and check 47 transitive
axiom reports, permitting only `propext`, `Classical.choice` and `Quot.sound`:

- CDF coupling: [11 exact statements](arbitrary_law_cdf_coupling.lean) and
  [11 reports](arbitrary_law_cdf_coupling.log).
- Zero-atom functional and comparison: [36 exact statements](arbitrary_law_zero.lean)
  and [36 reports](arbitrary_law_zero.log).

## Checked scope

The generalized inverse of a right-continuous CDF pushes uniform volume on
the unit interval to its bounded nonnegative probability law. Two inverses
driven by the same uniform variable form a probability coupling with the
specified marginals. CDF domination makes it increasing. The proof includes
atoms, in particular mass at zero, and verifies the exact threshold identity.

For laws on `[0,1/2]`, the extended entropy is infinite when the selected
measure has positive mass at zero; the tail kernel at zero is one. The
original infimum over all fractional submeasures is retained. Gamma, the
objective and K agree exactly with the earlier positive-gap functional
after embedding a finite positive-gap measure into the real line.

Increasing couplings give factor-three entropy and square-root-three
selection comparisons, preserving selected mass and domination. Combining
this with the constructed CDF coupling proves
`F_new <= F_old` implies `K(new) <= sqrt(3) K(old)` for probability laws on
`[0,1/2]`. Neither a coupling witness, atomlessness, a finite inverse moment
nor finite entropy is assumed in the final theorem.

The light random contraction, dominated-mass inequality, learned-law
performance bounds, robust continuation and full statistical/controller
composition remain outside this checkpoint. The complete arbitrary-law
adaptation theorem remains a paper proof and Python execution is unverified.
See the [current scope](../../docs/ARBITRARY_LAW_FORMALIZATION.md).

## Replay

With the pinned Lean toolchain and Mathlib cache:

~~~sh
python tools/verify_arbitrary_law_cdf_coupling.py
python tools/verify_arbitrary_law_zero.py
~~~

All 1,137 Lean sources pass the source guard. The audit-validator and
source-guard regression suites pass 18 tests. Frozen-source, relative-link
and whitespace checks pass. CI is separate and must be identified by its
actual checked commit.
