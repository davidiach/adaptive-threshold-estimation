# RMS obstruction transfer and additive localization

This record verifies the generic RMS consequences of the
variance–null-work obstruction, including overlapping submeasures.

The proof checkpoint is
`8ed87544c861eee47a7b9fd2ede9483529b60e52`.
The base publication checkpoint is
`99cc6f756316d93aac1c9fbafdc4da3f316c2b9e`.

## Checked conclusions

For a known positive-gap law, $0<\rho\le1/4$, $B>0$, and a
variance–null-work obstruction $(b,J)$ with $b,J>0$,

\[
R_{\mu,\rho}(B)\ge128^{-1}\min\{b,\sqrt{J/B}\}.
\]

For finite nonzero submeasures $\sigma_i$ with
$\sum_i\sigma_i\le\mu$, masses $\tau_i$, normalized laws
$\nu_i$, and conditional obstructions $(b_i,J_i)$ at rarities
$0<r_i\le1/4$ satisfying $\sum_i\tau_i r_i\le\rho$,

\[
R_{\mu,\rho}(B)\ge
128^{-1}\sum_i\tau_i\min\{b_i,\sqrt{J_i/B}\}.
\]

Both bounds cover each admissible observable estimator and the
minimax infimum. The component supports may overlap, and the
empty component family is included.

## Native evidence

- 15 exact statements and 15 transitive axiom reports.
- 366 project modules in the dependency closure.
- Nine new modules compiled with empty diagnostic logs.
- 357 inherited compiled objects matched to published hashes.
- Source, direct-dependency object and output-object identities checked together.
- Only `propext`, `Classical.choice` and `Quot.sound` appear in the reports.
- The source guard checked all 992 Lean files.
- Frozen-source verification, 15 verifier regression tests and 12 manuscript regression tests passed.

The [status record](status.json) identifies all sources and compiled
dependencies. The [exact audit input](rms_localization.lean) and
[native log](rms_localization.log) record the 15 checks. The nine
numbered logs follow the fresh compilation order in the status file.

## Original observation model

The proof passes from finite population trees to arbitrary private
seeds and natural-number coin labels. Local Hellinger losses are
charged to work under the common midpoint law. The original
experiment's terminal-affinity theorem uses each endpoint's finite
expected work to reconstruct its stopped transcript.

The strengthened binary bound shows that two testing errors at
most $1/4$ give affinity at most $7/8$. Affinity at least $9/10$
therefore forces maximum squared risk at least one sixteenth
of the squared target gap. The resulting RMS bound is one quarter
of that gap.

The additive theorem reuses the exact global-prior, observation-law
and work construction for overlapping submeasures. The
[proof map](../../docs/RMS_LOCALIZATION.md) links all steps.

## Manuscript and remaining scope

The [162-page manuscript](../../paper/v6/builds/rms-localization-20261105.pdf)
contains both proofs. Its [build record](../../paper/v6/builds/rms-localization-20261105.json)
records two byte-identical offline builds, all four changed pages
visually inspected, 371 labels and 29 citations. There are no new
layout defects. All earlier records and PDFs remain preserved.

The sharp quantile-factor characterization retains its paper proof.
The open research questions are listed in the
[workplan](../../docs/WORKPLAN.md#current-priorities).
Human specialist review remains absent.
