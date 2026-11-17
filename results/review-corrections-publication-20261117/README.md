# Publication of the review corrections

The [192-page manuscript](../../paper/v6/builds/review-corrections-20261117.pdf)
typesets the v6 sources after the corrections of a line-by-line review of
the paper's text, merged in
[#120](https://github.com/davidiach/adaptive-threshold-estimation/pull/120).
That change touches no proof, Lean source, lock or status entry. The status
table keeps 32 Lean-checked entries and one paper-proof entry.

This record covers typesetting only. The review was a read-through of the
text and is recorded in #120. It is not a proof audit, and it does not
change the verification status of any result.

## Corrections in the text

One correction widens a stated range. The others make no statement stronger.

| Location | Pages | Correction |
|---|---|---|
| §11.3 | 31 | The uniform power-margin theorem gives the confidence radii for exponents $0<\alpha\le4$, where the text said every exponent. |
| Appendix A | 66–67 | In the bounded-ratio lemma the hybrid law for coin $i$ is written $P^{(i)}$. The earlier $P_i$ collided at $i=1$ with the alternative law $P_1$. |
| Appendix B | 77 | The closing remark says that the global rarity constraint is used in integrated form in (B.3) and elsewhere only as $\theta\le\rho$. |
| Appendix E | 99 | The displayed upper constant $33000$ is a conservative rounding of coefficients below $27000$. |
| Appendix G | 108–112 | The gate lemma and the annular proposition state the range $0<\rho\le1/4$ that their proofs use. The inserted sentence reflows the rest of the appendix. |
| Appendices J–L | 126, 131 | The standing rarity range of the stopping programs is $0<\rho\le1/2$, the range that Appendix Q, §15 and Theorem S.1 use. The explicit cap $N_*$ keeps $\rho\le1/4$. |
| Appendix S | 155–156 | Theorem S.1 states $0<\rho\le1/4$ for the critical law. Its proof names the general-law base rule at an arbitrary allowance and covers base budgets below one. |
| Appendix U | 167 | The level count at exponent one uses the sharpened bias bound $4r_{k+J}/3$, with an explicit $J$. |
| Appendix V | 170 | Finiteness of the coefficient $C$ is equivalent to inverse-gap integrability, not weaker. |
| Appendix V | 181 | A reference zero atom costs its mass times the race cap $2M$ in work, not $M$. |

Lean states the four-prior duality and the cap-rate theorems for
$\rho\le1/2$ and the certificate for $N_*$ for $\rho\le1/4$, so the widened
range matches the checked statements.

## Source identity

The TeX sources are pinned to
[`97a501383083cc0fa64cb96405444048b8fd4053`](https://github.com/davidiach/adaptive-threshold-estimation/commit/97a501383083cc0fa64cb96405444048b8fd4053),
the merge of #120. The
[build record](../../paper/v6/builds/review-corrections-20261117.json)
lists the SHA-256 of all 59 TeX files, of `status.json` and of
`sources.json`. Ten TeX files differ from the previous build's checkpoint
[`cbfd73ef3d4a5db1481f9a55ce9e1640ad3c916b`](https://github.com/davidiach/adaptive-threshold-estimation/commit/cbfd73ef3d4a5db1481f9a55ce9e1640ad3c916b).
`status.json`, `sources.json`, the manuscript workflow and the 107 pinned
source links in the TeX files are the same at both checkpoints.

## How the PDF was built

The PDF comes from two local builds, not from a workflow artifact. Each
build ran in its own fresh copy of `paper/v6` at the source commit, with the
command and environment of the
[manuscript workflow](../../.github/workflows/manuscript.yml):

```sh
SOURCE_DATE_EPOCH=1793232000 FORCE_SOURCE_DATE=1 latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The two PDFs are byte-identical: 192 pages, 1,515,796 bytes, SHA-256
`9f98e4f9329f772764b6d818cbb1fe670ed52fb2af808d59e034a4b6c4a56af7`. The two
logs ([first](manuscript-build-1.log), [second](manuscript-build-2.log)) are
identical as well. The PDF has 33 embedded font objects, 402 unique source
labels and 29 resolved citations, and no unresolved or duplicate reference.
The only TeX warning is the inherited 5.16461 pt overfull line in
Appendix C.

[toolchain-validation.json](toolchain-validation.json) lists the TeX Live
packages, which come from the Ubuntu 24.04 archive as in the workflow. It
also records one check of that toolchain: it rebuilds the
[previous published PDF](../../paper/v6/builds/power-window-complete-20261116.pdf)
byte for byte from that PDF's recorded source commit.

## Workflow builds

[manuscript-ci.json](manuscript-ci.json) identifies three successful runs of
the manuscript workflow on the same sources: the push build of the source
commit on `main`, and the push and pull-request builds for `5dd314a`, the
head of #120, which has the same git tree as the source commit. Each job log
reports 192 pages and a file size of 1,515,796 bytes, the size of the
published PDF.

The workflow artifacts were not downloaded, because the build session could
not reach GitHub's artifact storage. This record therefore does not claim
byte identity between the published PDF and a workflow artifact.

## Page comparison

[page-comparison.json](page-comparison.json) compares the PDF with the
previous build. Seventeen pages differ, each holding one of the corrections
above. The other 175 pages retain identical extracted body text and word
positions. No page is relocated, and the table of contents is unchanged.

All 17 changed pages and contents page 2 were rendered with Poppler at
110 dpi and visually inspected. No clipping, overlap, missing text or
displaced header or footer was found.

## Scope

The proof evidence for the manuscript's claims is unchanged. It is that of
the [previous publication record](../power-window-publication-20261116/README.md)
and of the records in the [index](../README.md). This record adds no Lean
audit and no numerical experiment. The CI runs named here built the
manuscript at their own commits; they are not evidence about a later commit.

[SHA256SUMS](SHA256SUMS) identifies the files of this record, the PDF and
the build record. All earlier PDFs and records retain their original bytes.
