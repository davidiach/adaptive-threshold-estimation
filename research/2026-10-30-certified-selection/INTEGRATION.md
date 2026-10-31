# Integration and proof obligations

## Apply safely

Base commit: `6ad675e04570cc1ef6bece8e26beb81e1a176471`.

The companion `adaptive_threshold_improvements_2026-10-30.patch` adds new paths
only. From a disposable checkout at that commit, first inspect the working tree:

```sh
git status --short
git apply --check /path/to/adaptive_threshold_improvements_2026-10-30.patch
git apply /path/to/adaptive_threshold_improvements_2026-10-30.patch
python -m unittest discover -s toolkit/tests -p 'test_rare_event_functional.py' -v
python research/2026-10-30-certified-selection/verify_algebra.py
python research/2026-10-30-certified-selection/reproduce.py
```

The patch does not add the PDF; copy it from the archive or build it using
`build_pdf.sh`. It adds no import to the existing `threshold_toolkit/__init__.py`:
import the new module explicitly. No existing API or estimator is changed.

Patch syntax/application was tested against a clean temporary empty Git repository.
Application to the pinned full upstream checkout and the full existing suites
was **not** tested. The new paths were checked against the accessible source
layout, but a later branch may independently introduce a collision.

Do not rewrite upstream locks or published PDFs to accommodate this package.
Before merging into the project, run its existing freeze verifier and toolkit
suite in a disposable full checkout. This is an unperformed integration check,
not a claim that a new freeze or CI check has passed.

## Mathematical dependency graph

1. Entropy interaction (Lemma 1).
2. Scale-separated cost at coefficient two (Lemma 2).
3. Scalar comparison at coefficient 8/5 (Lemma 3).
4. Quantile-to-selection comparison (Theorem 4).
5. Bandwise suffix structure (Theorem 5) and global-cut approximation.
6. Total-variation stability and band-preserving rounding (Theorems 7–8).
7. Finite-law enclosure transfer (Corollary 9).

The entropy interaction, scale geometry, and scalar algebra are independent of
the observable coin experiment. The statistical interpretation of K is inherited
from the separate paper theorem, not proved here. The new comparison may improve
a deterministic constant without improving the main statistical rate exponent.

## Formalization targets, without changing current locked targets

Add an independent specification with exact canonical bands and the same K/Gamma
objects. State the total-variation convention explicitly. Prove the lemmas above
against those specifications before changing documentation's verification status.
The scalar lemma's four polynomial identities have a standard-library exact
coefficient checker, but the checker is not a substitute for a Lean proof.

For the suffix theorem, formalize the finite within-band exchange, concavity on
each fractional-knapsack segment, and the finite iteration over bands. Do not
replace the conclusion with an unproved single global threshold rule: the package
contains a strict counterexample to that stronger claim.

For approximation, retain the original band membership. The cross-boundary
counterexample rules out dropping that assumption from the multiplicative bound.
No claim about learning the magnitude law or reusing a misspecified estimator
follows merely from stability of K.

## Review limitations

Proofs and code were developed and checked in one assistant session. Numerical
full-subset checks use a different enumeration, but share arithmetic primitives.
Certificate replay shares the production implementation. None of these is an
independent specialist review or formal verification of the Python runtime.
The repository's preference not to make specialist review a completion gate is
preserved; its absence remains disclosed.
