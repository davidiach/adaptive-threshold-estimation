# Publication of the RMS upper constant 12

The [205-page manuscript](../../paper/v6/builds/upper-constant-12-20261119.pdf)
typesets the v6 sources with the upper constant of the RMS law that Lean
already checked. With $\omega_\mu(h)=\int\min(1,h/d)\,\mu(dd)$:

- **Theorem AB.1.** For each $B\ge1$ there is one algorithm, depending only
  on $B$, that uses at most $B$ expected observations and has RMS error at
  most $12\,\omega_\mu(B^{-1/2})$ for every gap law $\mu$ and every sign
  law. In particular $R_\mu(B)\le12\,\omega_\mu(B^{-1/2})$, and with the
  sharp lower constant $1/6$ of Theorem AA.1 the two sides of the RMS law
  are within the factor $72$. The previous build,
  [upper-constant-20261119](../../paper/v6/builds/upper-constant-20261119.pdf),
  stated $15$; Section 18 still records $512$ for the frozen target.

This record covers typesetting only. The proof evidence for the constant is
the [library audit record](../upper-scale-20261119/README.md) and the records
of the earlier stages that it extends.

## What changes in the text

| Location | Pages | Change |
|---|---|---|
| Contents | 3 | The title of Appendix AB: "The upper constant 12 of the RMS law". |
| §1.1, Verification boundary | 5 | Coefficient $12$. |
| §1.2, overview table | 6 | The RMS row states $12$ and cites Theorem AB.1 and Appendix AB. |
| §1.3, status table | 8 | `UpperScale/Full.lean` replaces `UpperSign/Full.lean` in the RMS-law row. |
| §1.4 | 10 | Appendices AA and AB prove the constants $1/6$ and $12$. |
| Theorem 2.1 and its formal scope | 12 | $C=12$ for RMS; the formal scope cites `blind_upper_12` and `minimax_upper_12`. |
| §5.2 | 19 | One sentence: Theorem AB.1 gives $C=12$ with one level calibrated at the scale $B/4$. |
| §18 | 54, 58–63 | The claim row of the RMS upper bound, the paragraph "The upper constant 12", and one sentence on Appendix AB, with reflow. |
| Appendix AA.5 | 195 | The closing remark: the two sides are within the factor $72$. |
| Appendix AB | 198–203 | Rewritten: Theorem AB.1 with $12$, Lemmas AB.2–AB.8 and their proofs, and what Lean checks. |

No page moved. Appendix AB keeps pages 198–203, and the references keep
pages 204–205. The other 184 pages have identical body pixels.

Appendix AB now proves the bound in three parts:

- **Calibration at $B/4$.** One level is calibrated with the denominator
  $B/4$, which need not be a power of two.
- **Call cost $26/5$.** A third offset bound, $399/100$, covers the grids of
  level difference at least three.
- **Call second moment $13/2$.**
  - The votes after $m$ and $2m$ flips change with probability exactly
    $a(1-a)\le1/4$.
  - The split is at $19/20$, with four bands of drift tables.

The status table keeps 33 entries: 32 Lean-checked and one paper proof.
`UpperScale/Full.lean` replaces `UpperSign/Full.lean` as evidence for the
RMS-law entry. The results that use the distribution-blind family of
Section 5 keep their stated constants: the confidence bound of Theorem 2.1,
and Appendices R, T and Z. Appendix AB outlines the Lean proof and states
which numerical certificates Lean checks; it does not repeat them.

## Review of the new text

Lean checks the theorem. The written text is separate. Before this build, a
reviewer that had not written it read Appendix AB and the changed passages
of Sections 2, 5 and 18 against the Lean proofs. It recomputed every
constant and found no mathematical error. Its findings:

- module attributions:
  - the reordering for $26/5$ is redone in `UpperCallCost`;
  - `UpperQuarter` exports the bound $1/4$ of the vote-change lemma, and its
    proof establishes the identity;
- the numerical study is of the dyadic estimator of Section 5, not of the new
  family;
- "the split" was used before it was defined;
- clashing symbols;
- the scaled batch uses $B$ less the mean cost of one call, not the whole
  budget;
- an unclear description of the marks and the production calls.

Commit
[`b1cff20`](https://github.com/davidiach/adaptive-threshold-estimation/commit/b1cff202deb9f36a4f4f1f7a7a78cc86660e0dd0),
the source commit, fixes them. This was a review by an AI agent. It is not a
specialist referee report.

## Source identity

The TeX sources are pinned to
[`b1cff202deb9f36a4f4f1f7a7a78cc86660e0dd0`](https://github.com/davidiach/adaptive-threshold-estimation/commit/b1cff202deb9f36a4f4f1f7a7a78cc86660e0dd0).
The [build record](../../paper/v6/builds/upper-constant-12-20261119.json)
lists the SHA-256 of all 61 TeX files, of `status.json` and of
`sources.json`. The sources pin one new revision,
[`eb9f1a19f59d7afe6145fa91b150321f49a2a1ef`](https://github.com/davidiach/adaptive-threshold-estimation/commit/eb9f1a19f59d7afe6145fa91b150321f49a2a1ef),
the Lean commit of the upper constant 12, for their seven links to
`lean/ThresholdHC/UpperScale/Full.lean`. They no longer link the Lean commit
of the constant 15.

## How the PDF was built

The PDF comes from two local builds, not from a workflow artifact. Each
build ran in its own fresh copy of `paper/v6` at the source commit, with the
command and environment of the
[manuscript workflow](../../.github/workflows/manuscript.yml):

```sh
SOURCE_DATE_EPOCH=1793232000 FORCE_SOURCE_DATE=1 latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The two PDFs are byte-identical: 205 pages, 1,612,227 bytes, SHA-256
`08eab6fa14e0d6f9ba9fa6b66e7a4cf522c1b9ad928a79cfd3414fc1bfc91709`. The two
logs ([first](manuscript-build-1.log), [second](manuscript-build-2.log)) are
identical as well. The PDF has 34 embedded font objects, 440 unique source
labels and 29 resolved citations, and no unresolved or duplicate reference.
The only TeX warning is the inherited 5.16461 pt overfull line in
Appendix C.

[toolchain-validation.json](toolchain-validation.json) lists the TeX Live
packages, which come from the Ubuntu 24.04 archive as in the workflow. The
same toolchain rebuilds the five previous published PDFs byte for byte from
their recorded source commits. The rebuild of
[upper-constant-20261119](../../paper/v6/builds/upper-constant-20261119.pdf)
was made for this build. The other four were made for that build, in the
same session. The earliest of them,
[power-window-complete-20261116](../../paper/v6/builds/power-window-complete-20261116.pdf),
was published from a workflow build.

## Workflow build

[manuscript-ci.json](manuscript-ci.json) identifies one successful run of
the manuscript workflow, for
[#148](https://github.com/davidiach/adaptive-threshold-estimation/pull/148)
at the source commit. Its job log reports 205 pages and a file size of
1,612,227 bytes, the size of the published PDF. Its only warning in the
final pass is the same overfull line. The workflow artifact was not
downloaded, because the build session could not reach GitHub's artifact
storage, so this record does not claim byte identity with it.

## Page comparison

[page-comparison.json](page-comparison.json) compares the PDF with the
previous build, `upper-constant-20261119`, by rendered pixels: each page at
100 dpi in grey, with a 60 pt band at the top and the bottom left out for
the running header and the page number. A page counts as unchanged only if
its body pixels are identical.

Twenty-one pages differ, as listed above. The other 184 pages have
identical body pixels at the same page numbers. The 21 changed pages were
rendered with Poppler at 100 dpi and visually inspected, in contact sheets
of four pages. No clipping, overlap, missing text or displaced header or
footer was found.

## Scope

This record adds no Lean audit and no numerical experiment. The proof
evidence for every other claim of the manuscript is unchanged: it is that
of the [previous publication record](../upper-constant-publication-20261119/README.md)
and of the records in the [index](../README.md). The CI run named here built
the manuscript at its own commit; it is not evidence about a later commit.

[SHA256SUMS](SHA256SUMS) identifies the files of this record, the PDF and
the build record. All PDFs and records that reached `main` retain their
original bytes.
