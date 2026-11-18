# Publication of the large-budget bracket and the 4B/9 cap

The [199-page manuscript](../../paper/v6/builds/large-budget-bracket-20261118.pdf)
typesets the v6 sources with two results that Lean already checked. With
$\omega_\mu(h)=\int\min(1,h/d)\,\mu(dd)$:

- **Theorem AA.7.** Let $c_{25}$ be the supremum of the constants $c$ with
  $R_\mu(B)\ge c\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge25$.
  Then $0.175198\le c_{25}\le0.186752$. The lower bound also holds for both
  magnitude oracles, and $0.17807955$ holds for $B\ge100$. Earlier builds
  stated $\sqrt{59/2100}\approx0.1676$ for $B\ge25$, which Theorem AA.1
  still proves.
- **Theorem Q.1.** For $k>1$, the optimized cap programs satisfy
  $P_N\le kG_N$ whenever $B\le N(k-1/k)^2$, so $N\ge4B/9$ gives
  $R\le P_N\le16R$. Earlier builds stated the cap $\lceil4B/3\rceil$.

This record covers typesetting only. The proof evidence for the bracket is
the [library audit record](../large-budget-rms-20261118/README.md), and for
the cap the [sharp RMS audit record](../sharp-rms-20261117/README.md).

## What changes in the text

| Location | Pages | Change |
|---|---|---|
| §1.2, overview table | 7 | The stopping-programs row states the cap $4B/9$. |
| §1.3, status table | 8 | `LargeBudgetRMS/Full.lean` joins the RMS-law row; `SquareRootCap/Full.lean` replaces `GenieRate/Full.lean` in the genie row. The table keeps its height. |
| §15, §17 | 49, 52 | The cap $4B/9$. |
| §18 | 57, 62–63 | The cap $4B/9$ with its Lean link, and one sentence on the audit of Appendix AA.6. That sentence adds three lines and moves lines to page 63. |
| Appendices L and N | 135, 139 | The cap $4B/9$. |
| Appendix Q | 152–153 | Theorem Q.1 and its proof, a paragraph on what Lean checks, and the opening and closing paragraphs of Q.1. |
| Appendix AA | 191, 195–197 | One sentence after Theorem AA.1, and the new §AA.6 with Theorem AA.7. |
| References | 198–199 | Moved from pages 196–197, with no change. |

The status table keeps 33 entries: 32 Lean-checked and one paper proof.
The two Lean files are added evidence for existing entries. The written
Appendix AA.6 outlines the Lean proof and states which certificates Lean
checks; it does not repeat them.

## Review of the new text

Lean checks both theorems. The written text is separate. Before this build,
a reviewer that had not written it read Appendix AA.6 and Appendix Q against
the Lean statements, recomputed every constant in exact or high-precision
arithmetic, and recomputed the pilot policy's risk polynomial from its
table; it matches the Lean coefficients. It found no mathematical error.
It found one sentence that the new Theorem Q.1 made false: Appendix Q.1
called the truncation bound the stronger comparison, but Theorem Q.1 gives
the smaller factor whenever $B\le4N$. It also found three unstated
conditions, one misleading description of the interval check, a letter used
for two quantities in Appendix Q, and symbols that clashed with Appendix AA.
Commit
[`a8b4e46`](https://github.com/davidiach/adaptive-threshold-estimation/commit/a8b4e46a5bc0147b88a1af7bb9f06e8c23e140d8)
fixes them. This was a review by an AI agent. It is not a specialist
referee report.

## Source identity

The TeX sources are pinned to
[`a8b4e46a5bc0147b88a1af7bb9f06e8c23e140d8`](https://github.com/davidiach/adaptive-threshold-estimation/commit/a8b4e46a5bc0147b88a1af7bb9f06e8c23e140d8).
The [build record](../../paper/v6/builds/large-budget-bracket-20261118.json)
lists the SHA-256 of all 60 TeX files, of `status.json` and of
`sources.json`. The sources pin one new revision,
[`7ed941f198939a95f282e491c66a2defeef0528b`](https://github.com/davidiach/adaptive-threshold-estimation/commit/7ed941f198939a95f282e491c66a2defeef0528b),
for their five links to `lean/ThresholdHC/LargeBudgetRMS`. Two new links
point to `lean/ThresholdHC/SquareRootCap/Full.lean` at the existing revision
`f142500`.

## How the PDF was built

The PDF comes from two local builds, not from a workflow artifact. Each
build ran in its own fresh copy of `paper/v6` at the source commit, with the
command and environment of the
[manuscript workflow](../../.github/workflows/manuscript.yml):

```sh
SOURCE_DATE_EPOCH=1793232000 FORCE_SOURCE_DATE=1 latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The two PDFs are byte-identical: 199 pages, 1,563,468 bytes, SHA-256
`4fcac1c7c123743eaf9be731bc9a63699632026656d4deb04f41d02dec661a5b`. The two
logs ([first](manuscript-build-1.log), [second](manuscript-build-2.log)) are
identical as well. The PDF has 33 embedded font objects, 425 unique source
labels and 29 resolved citations, and no unresolved or duplicate reference.
The only TeX warning is the inherited 5.16461 pt overfull line in
Appendix C.

[toolchain-validation.json](toolchain-validation.json) lists the TeX Live
packages, which come from the Ubuntu 24.04 archive as in the workflow. The
same toolchain rebuilds the three previous published PDFs byte for byte from
their recorded source commits. The earliest of them,
[power-window-complete-20261116](../../paper/v6/builds/power-window-complete-20261116.pdf),
was published from a workflow build.

## Workflow build

[manuscript-ci.json](manuscript-ci.json) identifies one successful run of
the manuscript workflow, for
[#132](https://github.com/davidiach/adaptive-threshold-estimation/pull/132)
at the source commit. Its job log reports 199 pages and a file size of
1,563,468 bytes, the size of the published PDF. Its only warning in the
final pass is the same overfull line. The workflow artifact was not
downloaded, because the build session could not reach GitHub's artifact
storage, so this record does not claim byte identity with it.

## Page comparison

[page-comparison.json](page-comparison.json) compares the PDF with the
previous build, `sharp-rms-constant-20261118`. Fifteen pages differ, as
listed above. The two reference pages are renumbered and otherwise
identical. The other 182 pages retain identical extracted body text and
word positions. Every section and subsection starts on the page it started
on; §AA.6 is new and starts on page 195.

The 15 changed pages, contents page 2 and the two reference pages were
rendered with Poppler at 100 dpi and visually inspected. No clipping,
overlap, missing text or displaced header or footer was found.

## Scope

This record adds no Lean audit and no numerical experiment. The proof
evidence for every other claim of the manuscript is unchanged: it is that
of the [previous publication record](../sharp-rms-constant-publication-20261118/README.md)
and of the records in the [index](../README.md). The CI run named here built
the manuscript at its own commit; it is not evidence about a later commit.

[SHA256SUMS](SHA256SUMS) identifies the files of this record, the PDF and
the build record. All PDFs and records that reached `main` retain their
original bytes.
