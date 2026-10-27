# Tier 5: unrestricted adaptive coin creation

The eight-hour-or-landmark goal began on 2026-10-27 at 08:19:16 UTC.
It extends the actual infinite-transcript information/work bound beyond the
fixed finite coin family of Tier 4. Earlier specifications and checkers remain
unchanged.

## Model and locked targets

Policies choose any natural-number coin label from the observed Boolean
history and a common random seed. A first observation of a label creates its
independent latent coin; later observations may revisit it in any order. There
is no allocation restriction or bound on the total number of labels. Magnitudes
and sign-prior perturbations may depend measurably on the common seed, allowing
arbitrary common random magnitude environments.

Each finite cylinder law is an explicit finite latent-sign mixture. Its cap is
computed from every label the finite decision tree can query, and may vary
without bound with the seed. Cap invariance and cylinder consistency must be
proved; they are not model assumptions. The realized-law condition identifies
bounded finite-prefix integrals and assumes no entropy or stopping conclusion.

The nine targets are normalization, cylinder consistency, actual finite-prefix
KL, plus-hypothesis halting from finite expected work, full KL as a prefix
supremum, the full information/work bound, its measurable-statistic corollary,
a realized unbounded fresh-coin example, and their combined theorem.
The example must have finite expected work but positive probability of
observing more than any prescribed number of distinct coins.

All three proof agents reviewed the statements before the 13-file
`TIER5_FROZEN.sha256` lock was created. The lock includes all prior lock manifests,
the specification's local import closure, the manifest, and the new verifier.

## New proof obligations

With unrestricted creation, finite expected work under the plus hypothesis
does not imply termination under the minus hypothesis. The new targets permit
minus-hypothesis nontermination. The entropy proof therefore uses generating
prefix sigma-algebras, convergence of conditional expectations of the
Radon--Nikodym derivative, and Fatou's lemma.

A separate likelihood comparison depends on the observation horizon rather
than the ambient number of coin labels: at horizon `n`, each direction of the
finite likelihood ratio is bounded by `(5/3)^n`. At most `n` distinct signs can
contribute; unused coins have likelihood factor one. This provides uniform
integrability bounds even when the seed-dependent finite cap is unbounded.

## Verification

The specifications compile, all three semantic reviews approve them, and the
eight new validation regression tests pass. The first foundations audit passes
**25/25 declarations**, including the horizon-only prior comparison and the
generic generating-filtration entropy theorem. No complete Tier 5 target is
claimed in this initial checkpoint; the exact process bridges and example remain
in progress.

Run `python tools/verify_tier5.py --sequential --require-complete` to require
all nine targets. Partial checkpoints omit `--require-complete` and must report
pending targets explicitly. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed.
