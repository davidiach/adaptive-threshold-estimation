# Consolidated version 6

[Current manuscript](builds/combined-psi-20261109.pdf) · [LaTeX sources](main.tex) · [Build record](builds/combined-psi-20261109.json) · [Previous build](builds/psi-closed-form-20261109.pdf)

The current build combines two builds that were published from the same base on 9 November 2026; see the [last section](#combined-build). The [closed-form and exposition build](#closed-form-and-exposition-build) adds [§14.8](psi-window.tex), which gives the variational modulus Ψ in closed form and the power-margin rate with constants uniform in the exponent, and revises the presentation: a rewritten abstract, a results overview with a generated status table, a reading guide and notation table, and a grouped table of contents. The [Psi lower bound build](#psi-lower-bound-and-tail-proof-build) records the arbitrary-law Ψ lower bound as Lean-checked and repairs one step of the arbitrary-law tail proof. The [earlier build](builds/status-coverage-20261107.pdf) added four results to the generated status paragraphs of the [arbitrary-law adaptation build](builds/arbitrary-law-adaptation-20261106.pdf), which combines the finite-gap menu and status-reconciliation changes with the arbitrary-law tail certificate and full eventual oracle-adaptation paper proof. The [finite-gap menu PDF](builds/gap-law-menus-20261105.pdf) and [status-reconciliation PDF](builds/status-reconciliation-20261105.pdf) retain their respective published source identities.

Later [Lean component audits](../../docs/ARBITRARY_LAW_FORMALIZATION.md) cover
the CDF and zero-atom comparison, dominated mass, the concrete factor-32
light contraction, the single-coin tail test of Appendix V.3 with its
error and work bounds, and its inverse-sampling step: one capped probe with
its coverage and performance bounds, the median certificate at one depth
and at every depth, its oracle comparison past a finite onset, the same
statements for an estimator that reads only observed flips, the capped
multi-depth pilot with the conservative law it learns, and the pilot's work
estimates and onset. The full arbitrary-law adaptation theorem remains a paper
proof; the published PDF and its build record retain their original scope.

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
| §1 | Introduction and related work. §1.2 summarizes the main results in one table, §1.3 lists the verification status of every tracked result, §1.4 describes how the sections and appendices fit together, and §1.5 collects the notation |
| §§2–10 | Version 5's original theory: model, minimax law, distribution-blind algorithm, unbiased characterization, 713 construction, power and boundary regimes, smoothness and observed-state results |
| §11 | Rare-event model, the variational modulus Ψ, the power-margin table (with a consistency check against the closed quantile form), and the critical quadratic law |
| §12 | Critical sign entropy for every finite gap count (the v5 all-size addendum) |
| §13 | The entropy–tail law for every magnitude law: definitions, theorem statements and proof structure |
| §14 | The closed quantile form: the finite-law theorem, its comparison with the selection functional, the extension to every law, and consequences |
| §14.8 | $\Psi$ in closed form within a factor $\sqrt2$, the $\Psi$ lower bound as a corollary of the entropy–tail law, the distance of $\Psi$ from the rate, and power-margin rates with constants independent of the exponent |
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
| Appendix V | Known-law time-uniform confidence, the matching lower bound, finite-family adaptation, and the arbitrary-law tail and oracle-adaptation paper proofs |
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
It also checks the arbitrary-law statistical Ψ lower bound of Appendix A,
with coefficient $10^{-17}$, as a corollary of the entropy–tail law.
It also checks the stochastic-envelope extension, lower-bound localization
with coefficient $1/128$ conditional on a single-coin obstruction, finite-menu cost grouping and finite-family oracle
adaptation. The [status table](../../docs/RESULTS.md#verification-status), generated
from [status.json](status.json), lists every result the abstract tracks.
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

[build_v6.py](../../tools/build_v6.py) generates 30 of the TeX files. Twenty-eight
come from the inputs hash-locked in [sources.json](sources.json): the v5
project files, the general-law v2 sections and bibliography, and the
finite-gap revision 2 sections. The other two, `status-abstract.tex` and
`status-table.tex`, and the introduction's Verification boundary paragraph
come from [status.json](status.json), the single source for those three
passages. The abstract counts the Lean-checked results and names each
paper-proof result, so it keeps its length as results are checked; the
status table of §1.3 lists every result with its Lean modules or the
location of its paper proof, and the boundary paragraph gives the scopes. To
change what they say about a result, edit its status and evidence paths
there and rerun the generator, then `python tools/build_status_docs.py`, which
regenerates the status sentence in the [README](../../README.md#scope-and-review)
and the status table in the [results guide](../../docs/RESULTS.md#verification-status); `tools/test_build_v6.py` rejects status
wording typed into the abstract or into a phrase. Section 18 keeps the exact
formal scopes and fixed source links and is edited by hand, but the
generator checks it against status.json: each claim-table row an entry
names must cite a Lean source for a Lean-checked result, or say paper and
cite no Lean source for a paper proof. The per-section status remarks are
still updated by hand. Each generated file begins with `% Generated by tools/build_v6.py`;
do not edit those files directly. Every other TeX file is hand-edited source:
the exposition in `frontmatter.tex`, `overview.tex` (§§1.2–1.5),
`rare-events.tex`, `entropy-tail.tex`,
`finite-laws.tex`, `psi-window.tex` (§14.8), `certificates.tex`,
`finite-proof.tex` and `verification.tex`; Appendices P–Z (`appendix-optimal-factor.tex` through
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
- **Addendum wording.** Version 5's all-size addendum referred to "the
  preserved critical-law proof" and its "existing" bounds. §12 cites
  Lemma C.3, Theorem C.2 and the tagged displays of Appendix C instead.
  The introduction says "the whole function" where v5 said "the entire
  function", and the proof outline of Appendix C no longer points to the
  v5 source manifest, whose provenance §18 records.
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
python tools/build_status_docs.py --check
python tools/check_build_record.py
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


## Finite-menu cost grouping

The verification table now includes the 14-statement Lean audit of the
mathematical finite-menu solver, its state and transition bounds, entropy
price, exact saving comparisons and interval certificates. It explicitly
leaves the concrete gap-law-to-menu construction and Python implementation
outside the formal result.

The new 166-page PDF has two byte-identical offline builds. Both changed
pages (38 and 45) were visually inspected; every other page is unchanged.
All 29 fonts are embedded, references resolve, and no new layout warning
appears. Earlier publications remain unchanged.

[Updated manuscript](builds/band-cost-formal-20261105.pdf) · [Build record](builds/band-cost-formal-20261105.json) · [Native audit](../../results/band-cost-formal-20261105/README.md)


## Square-root convergence of the ordinary cap program

Appendix Q.1 adds the output-preserving truncation proof and its checked
ordinary-program bound: $P_N\le(1+\sqrt{B/(N+1)})P_\infty$. The minimax
corollary gives factor sixteen once $N+1\ge B$. Optimality and the
corresponding genie convergence rate remain open.

The new 167-page PDF has two byte-identical offline builds. All three changed
pages (3, 46 and 140) were visually inspected; 27 following pages relocate
without body changes. All 29 fonts are embedded, references resolve, and no
new layout warning appears. Earlier publications remain unchanged.

[Updated manuscript](builds/finite-cap-truncation-20261105.pdf) · [Build record](builds/finite-cap-truncation-20261105.json) · [Native audit](../../results/finite-cap-truncation-20261105/README.md)


## Eventual adaptation within a finite candidate family

Section V.2 proves that a paid sign-neutral moment pilot identifies the true
member of a supplied finite family and then recovers its known-law time-uniform
rate beyond an explicit onset budget. Seventeen Lean statements verify the
parity, concentration, identification, probability-transfer and delayed-rate
components. Moment determinacy and the complete observable-controller
construction remained paper proofs at this checkpoint. Section V.4 now supplies a separate arbitrary-law oracle-adaptation paper proof.

The new 169-page PDF has two byte-identical offline builds. All four changed
pages (3, 50, 159 and 160) were visually inspected; nine later pages relocate
without body changes. All 29 fonts are embedded, references resolve, and no
new layout warning appears. Prior publications remain unchanged.

[Updated manuscript](builds/law-adaptation-20261105.pdf) · [Build record](builds/law-adaptation-20261105.json) · [Native component audit](../../results/law-adaptation-20261105/README.md)


## Shared-prefix refinement of the adaptation pilot

The current Section V.2 uses each coin's first 2m flips to supply all m parity
coordinates. The pilot therefore costs exactly 2mn flips on n fresh coins,
with the same error bound and oracle comparison. The existing Lean hypotheses
require independence across coins only, separately for each coordinate; they
already cover this refinement. The native proof checkpoint is unchanged.

The new 169-page PDF has two byte-identical offline builds. Both changed pages
(159 and 160) were visually inspected; no pages relocate. All 29 fonts are
embedded, references resolve, and no new layout warning appears. The earlier
publication and its record remain unchanged.

[Updated manuscript](builds/law-adaptation-shared-pilot-20261105.pdf) · [Build record](builds/law-adaptation-shared-pilot-20261105.json)


## Formal realization of finite-family adaptation

The current Section V.2 now has a complete Lean construction of the observable
pilot and selected confidence controller. A new 22-statement audit includes
moment determinacy and finite signature separation, actual shared-prefix
observations, unconditional caps and history compatibility, joint all-budget
coverage and oracle width, nesting, and the joint endpoint law in the original
observable experiment. Python execution and arbitrary-law oracle adaptation
remain outside this result.

The new 169-page PDF has two byte-identical offline builds. Both changed pages
(50 and 160) were visually inspected; no pages relocate. All 29 fonts are
embedded, references resolve, and no new layout warning appears. Earlier
publications and their records remain unchanged.

[Updated manuscript](builds/law-adaptation-realization-20261105.pdf) · [Build record](builds/law-adaptation-realization-20261105.json) · [Native proof record](../../results/law-adaptation-realization-20261105/README.md)


## Concrete finite-law selection menus

The verification table now records the formal connection from a finite gap
law to the cost-compressed suffix solver. Thirteen exact statements verify
menu coverage, disjointness, the original entropy and saving identities,
the optimized value K and the finite atomic sums. Python execution and the
unrestricted polynomial-time question remain outside the result.

The new 169-page PDF has two byte-identical offline builds. The only changed
page (45) was visually inspected; no pages relocate. All 29 fonts are embedded,
references resolve, and no new layout warning appears. Prior publications and
their records remain unchanged.

[Updated manuscript](builds/gap-law-menus-20261105.pdf) · [Build record](builds/gap-law-menus-20261105.json) · [Native proof record](../../results/gap-law-menus-20261105/README.md)

## Status reconciliation build

This build corrects verification-status statements that later appendices
had made stale: the abstract, the introduction's Verification boundary,
Sections 11 and 14 to 18, and Appendices K, N, O, Q, R and S. The abstract
status paragraph and the boundary paragraph are now generated from
[status.json](status.json), which also records the complete time-uniform
lower bound above as Lean-checked. Section 18 gains a table of the upper
constants 33000, 28000, 30001 and 28001. Section 2 and Section 18 now cite
the theorems whose types carry the coefficients 512 and 28000; the locked
targets assert only positive constants. No theorem changes. The
[model-fidelity brief](../../docs/MODEL_FIDELITY.md) compares the
manuscript's model with the Lean definitions.

The PDF has 167 pages. Two independent builds have identical bytes, all 29
fonts are embedded, there are no unresolved references, and the only
warning, an inherited overfull line, also occurs in the unchanged sources.
Tectonic was not available, so this build uses pdfTeX from TeX Live 2023,
the engine of the [manuscript workflow](../../.github/workflows/manuscript.yml),
with the same fixed source date. Pagination therefore differs from the
earlier Tectonic builds. The changed pages were found by comparing with the
sources of the time-uniform formalization build typeset by the same engine,
and all of them, with neighbouring pages, were visually inspected. The
record lists the inherited cosmetic issues seen.

[Updated manuscript](builds/status-reconciliation-20261105.pdf) · [Build record](builds/status-reconciliation-20261105.json)


## Arbitrary-law tail certificates

[Section V.3](arbitrary-law-tail.tex) proves an observable small-gap mass
certificate for every unknown probability law on positive gaps. A dyadic
single-coin test and capped inverse sampling give an explicit work envelope;
median amplification supplies the requested confidence. After a finite
law/rarity-dependent onset, the upper endpoint is at most $524288K(4^J)$
using $m4^J$ flips, where $m\ge8\log(2/\delta)$ is odd.

This new theorem is a paper proof with a tested Python controller, not a Lean
result. The [proof guide](../../docs/ARBITRARY_LAW_TAIL.md) states the full
scope. Core allocation, null-likelihood adaptation and a complete oracle-rate
interval are outside this tail-certificate result; Section V.4 now supplies
them in the separate paper proof below.

The 174-page build has two byte-identical offline builds and 29 embedded
fonts. Compared with a fresh build of the pre-change sources, pages 3, 52
and 163–165 change; later pages move by three. All changed pages were
visually inspected, references resolve, and the existing layout-warning
baseline is unchanged. Prior published PDFs and records remain unchanged.


## Eventual oracle adaptation for arbitrary unknown laws

[Section V.4](arbitrary-law-adaptation.tex) proves a single observable
confidence sequence for every unknown probability law on positive gaps,
with known rarity bound. It covers the positive fraction at every budget
and reaches the known-law oracle rate at the iterated-log effective budget
after a deterministic law-dependent onset. It requires no candidate family,
moment assumption, tail regularity, or supplied integration oracle.

The paid pilot learns a conservative finite law with an unresolved zero
atom. Entropy transport comparisons control its oracle value; a coupling
argument transfers the known-law estimator using correct-crossing times,
since total stopping work need not decrease when gaps increase. A fresh
capped-median continuation and summable stage allowances complete the
all-budget theorem. The [proof guide](../../docs/ARBITRARY_LAW_ADAPTATION.md)
gives the argument and executable interfaces. This new theorem is a paper
proof; its entropy, robustness and controller arguments are not Lean-checked.
The universal coefficient is conservative, and the onset is not uniform over
laws. No practical sample-complexity claim is made.

The 181-page manuscript has two byte-identical offline builds, 29 embedded
fonts, 379 unique labels and 29 resolved citations. All 15 changed pages were
visually inspected; nine following pages relocate by seven pages. No new
layout warning appears. The first-page wording is shortened to keep the
expanded status paragraph and provenance together. Earlier published PDFs
and build records, including the tail-certificate checkpoint, are unchanged.

[Updated manuscript](builds/arbitrary-law-adaptation-20261106.pdf) · [Build record](builds/arbitrary-law-adaptation-20261106.json) · [Tail-certificate checkpoint](builds/arbitrary-law-tail-20261106.pdf)

## Status coverage build

The abstract's status paragraph and the introduction's verification
boundary now also name four results that the manuscript already presents
with Lean citations: the stochastic-envelope extension, the $1/128$
localization transfers, finite-menu cost grouping with its concrete
finite-law menus, and finite-family oracle adaptation. Both paragraphs are
generated from [status.json](status.json); the menu entry is tied to its
Section 18 claim row. No theorem, proof or other passage changes. The
arbitrary-law adaptation components and the selection-approximation
components are not added, because the manuscript does not yet describe
them as checked.

The PDF has 180 pages. Two independent builds have identical bytes, all 29
fonts are embedded, there are no unresolved references, and the only
warning, an inherited overfull line, also occurs in the unchanged sources.
Tectonic was not available, so this build uses pdfTeX from TeX Live 2023,
the engine of the [manuscript workflow](../../.github/workflows/manuscript.yml),
with the same fixed source date. Against an unchanged-source baseline typeset
by the same engine, pages 1 and 6 gain the two generated sentences and page 7
absorbs text moved from page 6; the other 177 pages are identical and none is
renumbered. Pages 1, 2, 6 and 7 of this build were visually inspected. The
title page is nearly full, so the
[manuscript workflow](../../.github/workflows/manuscript.yml) now fails if the
abstract's last sentence or the provenance note leaves page 1, and
`python tools/check_build_record.py` checks that this record still describes
its PDF and the current sources.

[Updated manuscript](builds/status-coverage-20261107.pdf) · [Build record](builds/status-coverage-20261107.json)

## Closed form of Ψ and the critical window

[§14.8](psi-window.tex) is new mathematics, with paper proofs and no
independent review. Lean checks one part of it, the inequality
$\Psi\le\mathcal K$ with the two lower bounds of Corollary 14.10; see the
[Psi lower bound build](#psi-lower-bound-and-tail-proof-build). The rest is not
Lean-checked. It was first published in the
[closed-form and exposition build](#closed-form-and-exposition-build) below.

- **Ψ in closed form.** For every law, $\mathcal Q^0/\sqrt2\le\Psi\le\mathcal Q^0$,
  where $\mathcal Q^0$ is the closed quantile functional with the cost
  entropy of the quantile core replaced by its inverse-square cost. Both
  constants are attained.
- **The Ψ lower bound as a corollary.** $\Psi\le\mathcal K$ has a three-line
  proof, so the bounds of Theorem A.5 follow from the statements of the
  entropy–tail law and the confidence theorem, with constant $10^{-17}$, for
  every $B>0$, and without the Lee–Valiant input. That inequality is now
  Lean-checked, so the existing Lean results imply the Ψ lower bound.
- **Distance from the rate.** $\mathcal Q\le\sqrt{2(1+E_\kappa)}\,\Psi$, with
  $E_\kappa$ the entropy of the core's band costs, and a matching lower
  bound when the core term dominates. This says for which laws Ψ gives the
  rate, and by how much it fails otherwise.
- **Power margins, uniformly in the exponent.** For $F(d)=(d/a)^\alpha$ with
  $0<\alpha\le4$ an explicit formula gives the RMS rate and both confidence
  radii with constants independent of $\alpha$. For $3/2\le\alpha\le3$ the
  rate is $\min\{\rho,\ x\sqrt{\rho\,\Phi_\alpha(\rho)[1+\log N_\alpha(\rho)]}\}$.
  The earlier text said that the power-margin constants diverge as
  $\alpha\to2$ and claimed no uniform theorem; the remark after the
  corollary gives their growth, $\sqrt{\log(1/|\alpha-2|)/|\alpha-2|}$.

These results are tracked in [status.json](status.json) as one paper-proof
entry, so the abstract, the status table and the README tables list 31
results. §§11 and 18 point to the new statements where they stated the
old limits. The [check script](../../research/2026-11-09-psi-closed-form/README.md)
tests every inequality and constant in floating point; it is numerical
evidence, not a proof.

## Exposition revision

These source changes follow the status coverage build. They are published,
together with §14.8, in the
[closed-form and exposition build](#closed-form-and-exposition-build) below.

No theorem, proof or constant changes, and section, theorem and equation
numbers are unchanged. The changes are to the presentation:

- **Abstract.** The mathematical part is rewritten to state the problem, the
  worst case and each main result in plain terms. The generated status
  paragraph now counts the Lean-checked results and names the paper proofs,
  so it no longer lengthens the title page as results are checked.
- **§§1.2–1.5.** The new hand-written [overview.tex](overview.tex) gives a
  table of the main results with their locations, the generated status
  table, a guide to the sections and appendices, and a notation table that
  also lists the letters whose meaning differs between parts.
- **Contents.** Unnumbered group headings divide the 18 sections and 26
  appendices by topic.
- **Cross-references.** `cleveref` capitalizes every reference name, so the
  text no longer mixes "theorem 11.2" with "Theorem 13.2".
- **§12 and status remarks.** §12 cites Appendix C in place of "the
  preserved critical-law proof", and the status remarks of §§11, 13–15 and
  18 and of Appendices S and V drop "now" and "new".

The existing tables are renumbered from 1–3 to 4–6.

## Closed-form and exposition build

This build publishes the two preceding changes: §14.8 and the exposition
revision. The PDF has 192 pages, twelve more than the status coverage build:
five from the overview with its status table, six from §14.8, and one from
the additions to §18.

Two independent builds have identical bytes, all 33 fonts are embedded,
there are no unresolved references, and the only warning, an inherited
overfull line in Appendix C, also occurs in the unchanged sources. The
engine is pdfTeX from TeX Live 2023, that of the
[manuscript workflow](../../.github/workflows/manuscript.yml), with the same
fixed source date. This environment does not reproduce the status coverage
PDF byte for byte, so pages are compared with the unchanged sources typeset
here.

Against that baseline, 34 pages carry new or edited text, 34 have unchanged
text with page breaks moved by the insertions before them, and 26 differ
only in capitalized reference names. All 94 were visually inspected. The
other 98 pages reproduce baseline pages twelve pages later, with word
positions equal to within 0.01pt. A mechanical comparison of every word
box with the text block finds no line beyond the margins other than the
inherited one. The [build record](builds/psi-closed-form-20261109.json)
lists the pages of each kind.

The new statements have paper proofs only. The
[check script](../../research/2026-11-09-psi-closed-form/README.md) passes
on these sources; it tests the inequalities in floating point and is not a
proof. No Lean source changes, and the Lean proofs were not rebuilt for
this build.

[Updated manuscript](builds/psi-closed-form-20261109.pdf) · [Build record](builds/psi-closed-form-20261109.json)

## Psi lower bound and tail-proof build

Three things change. None alters a theorem statement.

- **Status of the Ψ lower bound.** [Theorem A.5](appendix-localization.tex),
  the arbitrary-law statistical Ψ lower bound, is now Lean-checked with
  coefficient $10^{-17}$ for the RMS risk and the confidence radius. The
  [Lean proof](../../lean/ThresholdHC/PsiSelection/Full.lean) compares
  $\Psi_{\mu,\rho}(B^{-1/2})\le\mathcal K_{\mu,\rho}(B)$ by Cauchy–Schwarz and
  applies the explicit entropy–tail lower bounds, so it needs no Lee–Valiant
  input. The abstract and verification-boundary paragraphs, generated from
  [status.json](status.json), the Section 11 remark and the Section 18 row say
  so. The paper proof in Appendix A is unchanged.
- **The $1/128$ localization entry.** Both generated paragraphs now call it
  conditional: each theorem takes a single-coin obstruction as a hypothesis.
- **A repaired step in Appendix V.** The adaptation proof cited a sharper
  terminal unresolved bound "from the tail proof", which had only a Chebyshev
  bound. [Section V.3](arbitrary-law-tail.tex) now states the Hoeffding form
  (AT6a), and [Section V.4](arbitrary-law-adaptation.tex) cites it.

The PDF has 180 pages. Two independent builds from commit `84d8bfa` have
identical bytes, all 29 fonts are embedded, there are no unresolved
references, and the only warning is the inherited overfull line. The engine
is pdfTeX from TeX Live 2023 with the fixed source date; typesetting the
previous sources in the same environment reproduced the previous build byte
for byte. Against that baseline, pages 1, 6, 25, 44, 162, 163 and 168 change
and the other 173 pages are identical; none is renumbered. Those seven pages
and page 2 were rendered and inspected. Earlier published PDFs and records
are unchanged.

[Updated manuscript](builds/psi-lower-bound-20261109.pdf) · [Build record](builds/psi-lower-bound-20261109.json)

## Combined build

The two preceding builds were prepared independently from the same base, so
neither contains the other's changes. This build typesets their merged
sources. Beyond what each build already contains, the merge changes four
passages:

- **Status source.** [status.json](status.json) lists 31 results: 29
  Lean-checked and 2 with paper proofs only, namely arbitrary-law oracle
  adaptation and the closed form of Ψ with the uniform power-margin rate.
  The abstract, the verification-boundary paragraph and the status table of
  §1.3 are regenerated from it.
- **§14.8.** Its status paragraph says that Lean checks $\Psi\le\mathcal K$
  and the two bounds of Corollary 14.10, and that the other statements have
  paper proofs.
- **§18.** The row for the general statistical Ψ lower bound cites the Lean
  theorems and refers to Corollary 14.10 for the derivation. The paragraph on
  paper proofs makes the same distinction for §14.8.

No theorem statement, proof or constant changes relative to the two builds.

The PDF has 192 pages. Two independent builds from commit `fef24b7` have
identical bytes, all 33 fonts are embedded, there are no unresolved
references, and the only warning is the inherited overfull line. The engine
is pdfTeX from TeX Live 2023 with the fixed source date. In the same
environment the Psi lower bound sources reproduce their published PDF byte
for byte. The closed-form sources give the same text as their published PDF
on all 192 pages but different bytes, so they are typeset here as the
baseline. Against that baseline 22 pages differ: 1, 6, 8–11, 30, 49–51,
55–63, 174, 175 and 180. The other 170 are identical in extracted text and as
rendered images, and none is renumbered. The 22 pages were rendered and
inspected for layout; the [build record](builds/combined-psi-20261109.json)
says what each contains. Earlier published PDFs and records are unchanged.

[Updated manuscript](builds/combined-psi-20261109.pdf) · [Build record](builds/combined-psi-20261109.json)
