# Publication of the release build

The [205-page manuscript](../../paper/v6/builds/release-20261119.pdf)
typesets the v6 sources with the corrections from the review of
19 November 2026. Its mathematical content is that of the
[previous build](../../paper/v6/builds/upper-constant-12-20261119.pdf),
`upper-constant-12-20261119`: the RMS law with the sharp lower constant
$1/6$ and the upper constant $12$, a factor $72$ apart, and every other
result unchanged. No statement, constant or proof step changes.

This record covers typesetting only. The proof evidence for every claim is
that of the [previous publication record](../upper-constant-12-publication-20261119/README.md)
and of the records in the [index](../README.md).

## What changes in the text

| Location | Pages | Change |
|---|---|---|
| §14.8, after Theorem 14.11 | 46 | The quadratic law of Theorem 11.2 exceeds $\Psi$ by the factor $\sqrt{1+\log L}$; the text said $1+\log L$, while the sentence before it and §11.4 already gave the square root. |
| §14.8, before Theorem 14.13 | 48 | $Y_\alpha(x,\rho)$ is defined for every $x>0$, as Corollary 14.14 and its proof use it; $T_\alpha(x,\rho)$ stays defined for $x<s_\rho$. |
| Appendix AB, introduction | 198 | The dyadic batch that the calibration at $B/4$ improves on uses as little as about $B/2$ minus the mean cost of one call, not $B/2$. |
| Appendix AB, after the proof of Theorem AB.1 | 199 | The bound $\lambda<2$ times $\omega_\mu((B/4)^{-1/2})^2$ is on the square of the bias. |
| Appendix AB.4 | 203 | The values Lean does not check include the decimal bounds $5.19$, $0.401$ and $6.49$, for which it checks $26/5$, $41/100$ and $13/2$. The closing remark cites the [numerical study](../../research/2026-11-19-upper-constant-12/README.md) of the family of Theorem AB.1, whose worst ratio is near $5.4$ and whose exact one-call constants are near $2.2$ and $3.6$, in place of the earlier study of the dyadic estimator of §5. |

No page moves. Appendix AB keeps pages 198–203, and the references keep
pages 204–205. The other 200 pages have identical body pixels.

The first four changes come from
[#152](https://github.com/davidiach/adaptive-threshold-estimation/pull/152).
The fifth is the source commit itself, which also brings the last lines of
Appendix AB back onto page 203: with only the changes of #152, they spilled
onto a new page 204.

## Review of the text

Before these changes, two AI reviewers that had not written the text read
Appendix AB against the Lean proofs and recomputed its constants, and read
Corollary 14.14 and Remark 14.15 of §14.8, the one tracked result with a
paper proof only, checking every inequality numerically over the whole
parameter range. Neither found a mathematical error. The wording slips they
found are the changes above. This was a review by AI agents. It is not a
specialist referee report.

## Source identity

The TeX sources are pinned to
[`a8b2324596009abe58db8cbe39434246722fc03d`](https://github.com/davidiach/adaptive-threshold-estimation/commit/a8b2324596009abe58db8cbe39434246722fc03d).
The [build record](../../paper/v6/builds/release-20261119.json) lists the
SHA-256 of all 61 TeX files, of `status.json` and of `sources.json`. Every
pinned source link to a Lean commit is the same as in the previous build.

## How the PDF was built

The PDF comes from two local builds, not from a workflow artifact. Each
build ran in its own fresh copy of `paper/v6` at the source commit, with the
command and environment of the
[manuscript workflow](../../.github/workflows/manuscript.yml):

```sh
SOURCE_DATE_EPOCH=1793232000 FORCE_SOURCE_DATE=1 latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The two PDFs are byte-identical: 205 pages, 1,612,581 bytes, SHA-256
`8cdf0b7bbf3f4b61bae924619d039f4e7e01be25a65bdc415755b894ffaf381f`. The two
logs ([first](manuscript-build-1.log), [second](manuscript-build-2.log)) are
identical as well. The PDF has 34 embedded font objects, 440 unique source
labels and 29 resolved citations, and no unresolved or duplicate reference.
The only TeX warning is the inherited 5.16461 pt overfull line in
Appendix C.

[toolchain-validation.json](toolchain-validation.json) lists the TeX Live
packages, which come from the Ubuntu 24.04 archive as in the workflow; their
versions are those of the previous record. Before this build, the same
toolchain rebuilt all six previous published PDFs byte for byte from their
recorded source commits, from
[power-window-complete-20261116](../../paper/v6/builds/power-window-complete-20261116.pdf),
which was published from a workflow build, to
[upper-constant-12-20261119](../../paper/v6/builds/upper-constant-12-20261119.pdf).

## Workflow build

[manuscript-ci.json](manuscript-ci.json) identifies one successful run of
the manuscript workflow, for
[#155](https://github.com/davidiach/adaptive-threshold-estimation/pull/155)
at the source commit. Its job log reports 205 pages and a file size of
1,612,581 bytes, the size of the published PDF, and the same single overfull
line. The workflow artifact was not downloaded, because the build session's
network policy blocks GitHub's artifact storage, so this record does not
claim byte identity with it.

## Page comparison

[page-comparison.json](page-comparison.json) compares the PDF with the
previous build, `upper-constant-12-20261119`, by rendered pixels: each page
at 100 dpi in grey, with a 60 pt band at the top and the bottom left out for
the running header and the page number. A page counts as unchanged only if
its body pixels are identical. [pixcmp.py](pixcmp.py) is the script that
made the comparison; run on the two builds before the previous one, it
reproduces that record's 21 changed pages.

Five pages differ, as listed above, and each has an edited passage. The
other 200 pages have identical body pixels at the same page numbers. The
five changed pages were rendered with Poppler and visually inspected. No
clipping, overlap, missing text or displaced header or footer was found.

## Scope

This record adds no Lean audit and no numerical experiment. The CI run named
here built the manuscript at its own commit; it is not evidence about a
later commit.

[SHA256SUMS](SHA256SUMS) identifies the files of this record, the PDF and
the build record. All PDFs and records that reached `main` retain their
original bytes.
