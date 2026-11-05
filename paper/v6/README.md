# Consolidated version 6

[Read the updated manuscript](builds/status-reconciliation-20261105.pdf) · [Open the LaTeX project](main.tex) · [Current build record](builds/status-reconciliation-20261105.json)

This is the current single research paper. It combines three manuscripts:

- the [consolidated v5 paper](../v5/README.md): the original minimax law,
  unbiased characterization, 713 construction, confidence and oracle lower
  bounds, power-margin rare-event regimes, and the critical quadratic law;
- the [general-law rare-event manuscript, revised v2](../rare-event/README.md):
  the entropy–tail characterization for every known magnitude law, the
  four-prior stopping dual and the finite certificates;
- the [finite-gap rare-event manuscript, revision 2](../finite-gap-rare-events/revision-2/README.md):
  the closed quantile formula, its direct proof for finite laws, and its
  comparison with the general-law selection functional.

All three source manuscripts, their PDFs and their review records are
unchanged.

## Reading guide

| Location | Contents |
|---|---|
| §§1–10 | Version 5's original theory: model, minimax law, distribution-blind algorithm, unbiased characterization, 713 construction, power and boundary regimes, smoothness and observed-state results |
| §11 | Rare-event model, the variational modulus Ψ, the power-margin table (with a consistency check against the closed quantile form), and the critical quadratic law |
| §12 | Critical sign entropy for every finite gap count (the v5 all-size addendum) |
| §13 | The entropy–tail law for every magnitude law: definitions, theorem statements and proof structure |
| §14 | The closed quantile form: the finite-law theorem, its comparison with the selection functional, the extension to every law, and consequences |
| §15 | Stopping programs, the four-prior dual, the factor-sixteen comparison and finite certificates |
| §§16–17 | Related work for the rare-event results; consequences and limits |
| §18 | Exact formal verification scope, with fixed Lean links |
| Appendices A–C | v5's rare-event localization, above-two construction and full critical proof |
| Appendices D–E | Proofs of the entropy–tail upper and lower bounds |
| Appendices F–H | Shared single-unit and transfer tools used by both rare-event proofs |
| Appendices I–N | Stopping-flow representation, exact dual, midpoint comparison, genie certificates, fixed-cap identification and exact numerical certificates |
| Appendix O | The direct proof of the closed quantile law for finite laws |
| Appendix P | The optimal general-law quantile comparison factor, its scalar equation and rational numerical bracket |
| Appendix Q | A uniform convergence rate for the optimized cap programs |
| Appendix R | RMS guarantees under a deterministic observation cap |
| Appendix S | Rare-event confidence at the effective budget, with subsections on adaptively selected component types, common pairs, fractional-submeasure localization, the sharper general-law confidence coefficient and RMS localization |
| Appendices T–U | The direct proof below margin exponent one; the logarithmic and intermediate power-margin rows |
| Appendix V | Observable time-uniform confidence for a known gap law |
| Appendix W | The smooth-density theorem in the adaptive experiment |
| Appendices X–Z | Observed states: the finite-cell lower bound, continuous-magnitude lower bounds and the fresh-outer-state upper-bound transfer |

## Verification status

Lean checks both directions of the original RMS law, the critical quadratic
law, the exact Ψ comparison and counterexample, the variational optimizer,
the unbiased characterization with constants 1/16 and 713, the confidence
characterization, the magnitude-oracle lower bounds, and the rare-event
rate above exponent two. It also checks both halves and the full entropy–tail
law, the two-sided closed quantile rate for every law, the comparison
$K\le Q\le(31/20)K$ and the exact least comparison factor of Appendix P,
and the existence of a finite-law optimizer that selects
a suffix in each dyadic band. For arbitrary laws it checks variation and
rounding stability and the finite-approximation enclosures. It also checks the stopping-program, fixed-cap
identification and genie results of §15, in the scope stated in §18.
Section 18 states each formal scope and links the fixed source revisions.

For finite laws a [direct Lean proof](../../lean/ThresholdHC/FiniteQuantile/Full.lean)
now establishes both explicit coefficients, $10^{-20}$ and $30001$. The
[operational theorems](../../lean/ThresholdHC/FiniteQuantile/Operational.lean)
give the estimator and converse statements. The [arbitrary-law comparison](../../lean/ThresholdHC/EntropyTailSharp/Full.lean)
checks $10^{-17}\mathcal K\le R\le28000\mathcal K$ and $10^{-17}Q\le R$.
The rare-event rows below two are now Lean-checked in [Appendix T](appendix-sublinear-power.tex) and [Appendix U](appendix-shifted-power.tex). [Appendix W](appendix-smooth-density.tex) gives the Lean-checked smooth-density complexity and unbiased-impossibility theorem. [Appendix X](appendix-finite-observed.tex) verifies the finite-cell observed-state lower bound. [Appendix Y](appendix-continuous-observed.tex) verifies the continuous-magnitude lower bounds and regularity. [Appendix Z](appendix-observed-upper.tex) verifies the fresh-state upper-bound transfer and completes both observed-state complexity rates.
The general-law and finite-gap proofs share
their upper construction and Appendices F–H, so they are one rate
established by two arguments, not two independent confirmations. The remark
in §11 on agreement of the power-margin table with the closed quantile form is
new in this edition; it is a consistency check, not additional verification.

## Source and editorial scope

[build_v6.py](../../tools/build_v6.py) generates 29 of the TeX files. Twenty-eight
come from the inputs hash-locked in [sources.json](sources.json): the v5
project files, the general-law v2 sections and bibliography, and the
finite-gap revision 2 sections. The twenty-ninth, `status-abstract.tex`, and
the introduction's Verification boundary paragraph come from
[status.json](status.json), the single source for those two passages. To
change what they say about a result, edit its status and evidence paths
there and rerun the generator; `tools/test_build_v6.py` rejects status
wording typed into the abstract or into a phrase. Section 18 keeps the exact
formal scopes and fixed source links and is edited by hand, but the
generator checks it against status.json: each claim-table row an entry
names must cite a Lean source for a Lean-checked result, or say paper and
cite no Lean source for a paper proof. The per-section status remarks are
still updated by hand. Each generated file begins with `% Generated by tools/build_v6.py`;
do not edit those files directly. Every other TeX file is hand-edited source:
the exposition in `frontmatter.tex`, `rare-events.tex`, `entropy-tail.tex`,
`finite-laws.tex`, `certificates.tex`, `finite-proof.tex` and
`verification.tex`; Appendices P–Z (`appendix-optimal-factor.tex` through
`appendix-observed-upper.tex`); and the confidence subsections that
`appendix-known-confidence.tex` inputs (`typed-confidence.tex`,
`common-pair-confidence.tex`, `additive-confidence.tex`,
`entropy-confidence.tex` and `rms-localization.tex`). `main.tex` controls the
layout.

The editorial changes are explicit in the generator:

- **One copy of shared proofs.** The two rare-event manuscripts carried
  near-identical versions of three appendices (observable classification
  and Poisson allocation, one-unit null-work obstructions, and convex
  comparison with additive localization). Appendices F–H use the general-law
  versions, which prove the stronger sign-entropy constant 214 in place of
  257. Every clarifying paragraph that the finite-gap version added is
  spliced in, for example the renewal identity without independence of
  acceptance and cost, the conditional-independence correction for typed
  hybrids, the explicit finite-family minimax step and the Hellinger
  partition argument.
- **One upper construction.** The finite-gap upper bound was the general
  construction applied to the quantile split. Appendix O.2 keeps its theorem,
  its split, its explicit constant 30000 and its finite terminal level, and
  cites Appendix D for the construction.
- **Notation.** Squared Hellinger distance is written 𝔥 throughout the
  shared appendices, as in the finite-gap manuscript, because h also
  denotes the budget scale. Finite-gap labels carry an `fg:` prefix.
- **Internal citations.** Citations of the companion manuscripts become
  cross-references. The finite-gap manuscript's conditional remark on
  general laws becomes a corollary in §14, whose proof cites the
  entropy–tail theorem in the same paper.
- **Superseded statements.** v5 passages saying that an arbitrary-law
  rare-event characterization remains open now point to §13. The
  verification section adds the above-two Lean result at
  `637fb4a79d20e30415a2cb0e495752603077c0ee`, and the entropy–tail upper
  half, closed quantile upper bound and stopping-program results at
  `8fb16244ded0d6cebf4ba78e1ad9adae09ef293d`. The completed lower half and
  two-sided law are pinned to `24937929f7c215d0f9b60c45083c0456d3d1fb31`.

[test_build_v6.py](../../tools/test_build_v6.py) checks that every line of
the finite-gap and general-law versions of the shared appendices is present
in the merged appendices, apart from explicit lists of replaced lines, and
that the dropped finite-gap upper construction matches the general one. The
source check follows the input graph from `main.tex` and rejects missing or
unused files, duplicate labels, unresolved references and citations, uncited
references, and unbalanced environments.

## Reproduce

From the repository root:

```sh
python tools/build_v6.py
python tools/build_v6.py --check
python -m unittest discover -s tools -p 'test_build_v6.py' -v
```

To build the PDF, copy `paper/v6/` to a disposable directory and run there:

```sh
SOURCE_DATE_EPOCH=1793232000 FORCE_SOURCE_DATE=1 latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The [manuscript workflow](../../.github/workflows/manuscript.yml) builds it
the same way with TeX Live from the Ubuntu 24.04 archive and uploads the PDF
and log as the `v6-paper` artifact. Typesetting and source checks do not
constitute a new mathematical proof or independent review.

## Hard-budget RMS build

Appendix R proves the hard-budget reduction and records the constants for
the three applications. The [Lean record](../../results/hard-budget-rms-20261104/README.md)
audits the observable experiment, its cap and risk. The [PDF build record](builds/hard-budget-rms-20261104.json)
lists the source hashes and changed pages.

## Critical confidence and cap-rate build

Appendix Q gives a quantitative comparison of the optimized ordinary and
latent-reveal programs. A cap of $\lceil4B/3\rceil$ already guarantees the
factor-sixteen risk certificate for every gap law. Section 18 records the
[formal cap theorem](../../results/genie-rate-20261104/README.md) and the
[critical-law confidence lower bound](../../results/critical-confidence-20261104/README.md).
The [build record](builds/critical-confidence-cap-rate-20261104.json) gives
the hashes of the typeset sources and PDF and records the visual checks.

## Optimal quantile factor build

Appendix P proves that the best factor for all positive-gap laws is a unique
scalar root. It also gives matching finite-law constructions. The
[rational certificate](../../tools/verify_optimal_quantile_factor.py) puts the
root strictly between $1.462554551279$ and $1.462554551280$. Section 18
records the [Lean proof of the upper bound $31/20$](../../results/quantile-price-20261104/README.md).
The sharp characterization has a paper proof.

The [published PDF](builds/optimal-quantile-factor-20261104.pdf) has 139 pages.
Two independent builds produced identical bytes. The [build record](builds/optimal-quantile-factor-20261104.json)
lists the source hashes, changed pages and visual checks.

## Population confidence build

Page 50 of the [updated paper](builds/confidence-population-20261104.pdf)
records the one-type KL transfer through unbounded stopping and the $1/128$
confidence lower bound under the common-pair premise. The [kernel audit](../../results/confidence-population-20261104/README.md)
and [build record](builds/confidence-population-20261104.json) identify the exact inputs.

## Confidence follow-up build

Page 50 of the [updated paper](builds/confidence-followups-20261104.pdf)
distinguishes the [Lean quarter-smoothing theorem](../../results/quarter-smoothing-20261104/README.md)
from the [unknown-law confidence sequence and time-uniform lower bound](../../docs/UNKNOWN_LAW_CONFIDENCE.md)
proved on paper. The [build record](builds/confidence-followups-20261104.json)
lists the pinned revisions and matching hashes of two offline builds.

## Selection stability build

Sections 14 and 18 of the [updated manuscript](builds/selection-stability-20261104.pdf)
locate Theorems 7 and 8 and the finite-approximation corollary.
The [Lean audit](../../results/selection-stability-20261104/README.md) checks
the approximation construction and both numerical enclosures. The [build
record](builds/selection-stability-20261104.json) identifies the source and PDF
hashes, the two identical builds, and the eight pages reviewed.

## Quantile comparison and finite selection build

The [4 November manuscript](builds/quantile-selection-suffix-20261104.pdf)
gives the sharper comparison and the finite-law suffix search bound in §14.
Section 18 links the Lean statements. The [build record](builds/quantile-selection-suffix-20261104.json)
records the pinned proof revisions, matching hashes from two offline builds,
embedded fonts and the pages reviewed.

## Explicit general-law build

The [updated PDF](builds/entropy-tail-explicit-20261104.pdf) records the
explicit arbitrary-law comparison in §§13 and 18. The theorem links use
proof revision `8a701c8db6c42930ad2a187f3d895ca55265afd6`. Two offline builds
produced identical PDFs. The [build record](builds/entropy-tail-explicit-20261104.json)
gives the source and PDF hashes, page count, font checks and visual review.

## Finite-law build

The [4 November PDF](builds/direct-finite-quantile-20261104.pdf) records the
finite-law theorem and its direct lower proof in §§14 and 18. The new theorem
links use proof commit `fc61852123b37c723bbb671d0b4ed294d3b6ee06`.
Two offline Tectonic builds produced identical 136-page PDFs. All 29 fonts
are embedded, the references resolve, and the final TeX warnings match the
1 November build. The [build record](builds/direct-finite-quantile-20261104.json)
identifies the exact inputs, PDF and pages inspected.

## Completion build

The [updated PDF](builds/entropy-tail-complete-20261101.pdf) records the
completed entropy-tail and general-law closed-quantile proofs. Its new theorem
links are pinned to `24937929f7c215d0f9b60c45083c0456d3d1fb31`. The
[build record](builds/entropy-tail-complete-20261101.json) identifies every
TeX source by its exact hash and preserves the earlier PDF's identity.

Two fresh scratch builds with Tectonic 0.17.0 and the fixed source date were
byte-identical: 136 pages and 788,463 bytes. All 29 fonts are embedded,
and there are no unresolved references or new TeX warnings. The inherited
critical-appendix overfull line and bibliography underfull line match the
unchanged-source baseline under this engine. The changed verification pages
were rendered and inspected; they have no new layout defects. Different
engines may paginate differently from the preserved pdfTeX build below.

## Preserved build record

The tracked `paper.pdf` below preserves the earlier published checkpoint.
The updated sources include the later entropy-tail completion; the
[manuscript workflow](../../.github/workflows/manuscript.yml) rebuilds them
in a scratch directory and publishes a `v6-paper` artifact for each matching
commit. That current artifact is separate from the preserved PDF.

`paper.pdf` was built from the v6 sources at commit
`ac1fbb75c94f97c90cc0887c4695eae7aece82db` with pdfTeX 1.40.25
(TeX Live 2023/Debian, Ubuntu 24.04 packages) and the fixed source date
above. Its SHA-256 is
`adfd7eec0af169f61a59839287604747b3503e8514b0102fba9cd3af1e4f7897`.

- Two consecutive builds in separate scratch copies were byte-identical:
  134 pages, 1,107,405 bytes. In the same environment, rebuilding `main`'s
  previous v6 sources reproduced the previously published PDF
  (`7ae803532ccc7946ac0d6c586a2f420dac5626066f613d3caed3963c20aa7a28`)
  byte for byte.
- The log has no LaTeX or package warnings and no undefined or duplicate
  references. The one overfull line, 5.2 pt in the inherited proof of
  Theorem C.1 (page 72), is unchanged.
- All 29 fonts are embedded, and the extracted text has no unresolved `??`
  references.
- Compared with the previous PDF, the extracted text differs on pages 1,
  31–33 and 38–47:
  - the abstract and the status paragraphs of §§13–15;
  - §§16–17, which reflow;
  - the verification section, §18.

  These pages were read as rendered pages. The seven new theorem links point
  to files at `8fb16244ded0d6cebf4ba78e1ad9adae09ef293d` that contain the
  named theorems.

A fresh build with another engine or TeX Live release may differ in bytes.

## Known-law fixed confidence

[Appendix S](appendix-known-confidence.tex) proves a direct stopping-program
lower bound and constructs the budgeted median in the observable experiment.
[Updated manuscript](builds/known-law-confidence-20261104.pdf) ·
[Build record](builds/known-law-confidence-20261104.json)

The [stochastic-envelope build](builds/stochastic-envelope-20261105.pdf)
adds the formal verification links for the corollary in the original
finite-budget and unbiased models. [Build record](builds/stochastic-envelope-20261105.json)

[Appendix T](appendix-sublinear-power.tex) gives a direct proof for power margins below one, including fixed confidence and a uniform upper estimator. [Manuscript](builds/sublinear-power-20261105.pdf) · [Build record](builds/sublinear-power-20261105.json)

[Appendix U](appendix-shifted-power.tex) gives the complete logarithmic and intermediate power-margin proofs. [Manuscript](builds/shifted-power-20261105.pdf) · [Build record](builds/shifted-power-20261105.json)

[Appendix V](appendix-anytime.tex) completes the known-law time-uniform upper theorem. [Manuscript](builds/anytime-confidence-20261105.pdf) · [Build record](builds/anytime-confidence-20261105.json)

[Appendix W](appendix-smooth-density.tex) completes smooth-density robustness. [Manuscript](builds/smooth-density-20261105.pdf) · [Build record](builds/smooth-density-20261105.json)

[Appendix X](appendix-finite-observed.tex) completes the finite-cell observed-state theorem. [Manuscript](builds/finite-observed-20261105.pdf) · [Build record](builds/finite-observed-20261105.json)

[Appendix Y](appendix-continuous-observed.tex) verifies continuous-magnitude observed-state lower bounds and regularity. [Manuscript](builds/continuous-observed-lower-20261105.pdf) · [Build record](builds/continuous-observed-lower-20261105.json)

[Appendix Z](appendix-observed-upper.tex) completes the observed-state upper bounds. [Manuscript](builds/observed-state-upper-20261105.pdf) · [Build record](builds/observed-state-upper-20261105.json)

[Selected-type transfer](typed-confidence.tex) extends the known-law confidence appendix with the full randomized, countable-label, unbounded-stopping proof. Common-pair derivation and fractional-submeasure localization retain their paper proofs. [Manuscript](builds/adaptive-types-20261105.pdf) · [Build record](builds/adaptive-types-20261105.json)

[Common-pair construction](common-pair-confidence.tex) proves the coefficient 42 from the variance–null-work obstruction and gives the $1/128$ confidence consequence. The regularization argument includes endpoint gap atoms. [Manuscript](builds/common-pair-20261105.pdf) · [Build record](builds/common-pair-20261105.json)

[Fractional-submeasure confidence localization](additive-confidence.tex) proves the additive coefficient $1/128$ with overlapping supports and an exact transfer to the original observation model. [Manuscript](builds/additive-confidence-20261105.pdf) · [Build record](builds/additive-confidence-20261105.json)

[Sharper general-law confidence](entropy-confidence.tex) proves the lower coefficient $10^{-17}$ through a direct stopping-program comparison and retains the hard-cap upper coefficient $750000$. [Manuscript](builds/entropy-confidence-20261105.pdf) · [Build record](builds/entropy-confidence-20261105.json)

[RMS obstruction transfer and additive localization](rms-localization.tex) verify coefficient $1/128$ using midpoint-work Hellinger bounds and binary testing. [Manuscript](builds/rms-localization-20261105.pdf) · [Build record](builds/rms-localization-20261105.json)

The unique scalar root and sharp finite-vector quantile factor are now Lean-checked in Appendix P. The arbitrary-law reduction and finite-law realization remain paper proofs. [Updated manuscript](builds/finite-vector-root-20261105.pdf) · [Build record](builds/finite-vector-root-20261105.json) · [Native record](../../results/optimal-quantile-root-20261105/README.md)

The entropy Lipschitz bound and sharp finite-core selection reduction in Appendix P now have native proofs. General-law measure normalization and finite-law realization remain paper proofs. [Updated manuscript](builds/quantile-core-reduction-20261105.pdf) · [Build record](builds/quantile-core-reduction-20261105.json) · [Native record](../../results/quantile-core-reduction-20261105/README.md)

The upper comparison at the exact scalar-root factor is now Lean-checked for every gap law. Finite-law sharpness remains a paper proof. [Updated manuscript](builds/sharp-quantile-upper-20261105.pdf) · [Build record](builds/sharp-quantile-upper-20261105.json) · [Native record](../../results/sharp-quantile-upper-20261105/README.md)

The exact scalar-root characterization, all-law comparison and finite-law sharpness in Appendix P are now Lean-checked. The decimal bracket retains separate rational verification. [Updated manuscript](builds/quantile-optimality-20261105.pdf) · [Build record](builds/quantile-optimality-20261105.json) · [Complete native record](../../results/quantile-optimality-20261105/README.md)

## Matching time-uniform lower-bound build

Appendix V.1 proves the matching gap-law-dependent lower bound on paper for
every positive-gap law, including infinite inverse moment. The native audit
checks 15 information inequalities; the sequential testing and asymptotic
comparison retain paper-proof status. The updated PDF has 168 pages.
Two independent builds have identical bytes; all eight changed pages were
visually inspected. Nine following pages move unchanged apart from their
page numbers. The build retains the two previously recorded layout warnings.

[Updated manuscript](builds/time-uniform-lower-20261105.pdf) · [Build record](builds/time-uniform-lower-20261105.json) · [Native record](../../results/anytime-lower-20261105/README.md)

## Complete time-uniform lower-bound formalization

Appendix V.1 now follows the complete Lean proof: first-crossing testing,
the infinite-moment prior construction and observable acquisition transfer,
finite-coefficient and dense/sparse asymptotic cases, and the interval
half-width consequence. The coefficient remains $10^{-22}$; a monotone
deterministic envelope is no longer required.

The new PDF has 166 pages. Two independent offline builds have identical
bytes. All five changed pages were visually inspected; nine following pages
move unchanged apart from page numbers. Every font is embedded, proof links
are pinned to the audited revision, and there are no unresolved references
or new layout warnings. The previous PDF and its record remain unchanged.

[Updated manuscript](builds/time-uniform-formal-20261105.pdf) · [Build record](builds/time-uniform-formal-20261105.json) · [Complete native record](../../results/anytime-asymptotic-20261105/README.md)

## Status reconciliation build

This build corrects verification-status statements that later appendices
had made stale: the abstract, the introduction's Verification boundary,
Sections 11 and 14 to 18, and Appendices K, N, O, Q, R and S. The abstract
status paragraph and the boundary paragraph are now generated from
[status.json](status.json). Section 18 gains a table of the upper constants
33000, 28000, 30001 and 28001. No theorem changes.

The PDF has 169 pages. Two independent builds have identical bytes, all 29
fonts are embedded, there are no unresolved references, and the only
warning, an inherited overfull line, also occurs in the unchanged sources.
Tectonic was not available, so this build uses pdfTeX from TeX Live 2023,
the engine of the [manuscript workflow](../../.github/workflows/manuscript.yml),
with the same fixed source date. Pagination therefore differs from the
earlier Tectonic builds. The changed pages were found by comparing with the
previous build's sources typeset by the same engine, and all of them, with
neighbouring pages, were visually inspected. The record lists the
inherited cosmetic issues seen.

[Updated manuscript](builds/status-reconciliation-20261105.pdf) · [Build record](builds/status-reconciliation-20261105.json)
