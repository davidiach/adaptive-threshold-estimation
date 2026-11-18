# Publication of the sharp RMS constant

The [197-page manuscript](../../paper/v6/builds/sharp-rms-constant-20261118.pdf)
typesets the v6 sources with the sharp constant of the RMS lower bound. For
every gap law and every $B\ge1$,

$$R_\mu(B)\ge\tfrac16\,\omega_\mu(B^{-1/2}),\qquad
\omega_\mu(h)=\int\min(1,h/d)\,\mu(dd),$$

and equality holds for the point law at gap $1/2$ and $B=4$. Earlier builds
stated the constant $1/64$.

This record covers typesetting only. The proof evidence for the new
constant is the [library audit record](../sharp-rms-20261117/README.md):
the Lean statements, their axiom reports and the kernel replay.

## What changes in the text

| Location | Pages | Change |
|---|---|---|
| Title page | 1 | The date is 18 November 2026. |
| Contents | 3 | A part heading and an entry for Appendix AA. |
| §1.1, verification boundary | 5 | Coefficients $1/6$ and $512$. |
| §1.2, overview table | 6 | The RMS-law row states $1/6$, says that it is sharp and cites Theorem AA.1. |
| §1.3, status table | 8 | The RMS-law row states $1/6$ (sharp) and lists `SharpRMS/Full.lean`. |
| §1.5, Notation | 10 | Appendix AA joins the places that write signs as $\pm1$. The paragraph keeps its line count. |
| Theorem 2.1 | 12 | One may take $c=1/6$ for RMS, which is sharp. The formal scope names the Lean theorem `sharp_lower`. |
| §18 | 62–63 | One sentence on the audit of Appendix AA. It adds three lines, so two lines move to page 63. |
| Appendix AA | 191–195 | New: the proof of the sharp constant, also under both magnitude oracles. |
| References | 196–197 | Moved from pages 191–192, with no change. |

The status table keeps 33 entries: 32 Lean-checked and one paper proof. The
sharp constant is added evidence for the existing RMS-law entry. §5 still
proves $1/64$, the coefficient of the frozen lower-bound target. The upper
constant $512$ is unchanged.

## Review of Appendix AA

Lean checks the theorem. The written proof in Appendix AA is separate
text, so it was read line by line by a reviewer that had not written it,
with the constants recomputed in exact arithmetic and the integer
certificate reimplemented from the appendix's description. That read found
no mathematical error. It found three steps whose justification the first
draft had dropped, one inaccurate sentence about how the Lean proof differs
from the written one, one display without its range, and notation that
clashed with the main text or within the appendix. Commits
[`cf08dc7`](https://github.com/davidiach/adaptive-threshold-estimation/commit/cf08dc78f285f1f3344a31d771b3e2462d3e481f)
and
[`c8c3001`](https://github.com/davidiach/adaptive-threshold-estimation/commit/c8c3001681a4fb99263ac99c74787ebbbc3673b3)
fix these, and the same reviewer re-read the result. No theorem, lemma,
constant or formula changed except by renaming symbols.

This was a review by an AI agent. It is not a specialist referee report.
Two cosmetic points remain as they were: the appendix writes $a=2d$ for a
flip bias, where §2 uses $a$ for the largest gap, and $r_s$ for a
single-gap risk, where §2 writes $r_\mu(B,\delta)$ for a confidence radius.
Both are defined where they are used.

## Source identity

The TeX sources are pinned to
[`c8c3001681a4fb99263ac99c74787ebbbc3673b3`](https://github.com/davidiach/adaptive-threshold-estimation/commit/c8c3001681a4fb99263ac99c74787ebbbc3673b3).
The [build record](../../paper/v6/builds/sharp-rms-constant-20261118.json)
lists the SHA-256 of all 60 TeX files, of `status.json` and of
`sources.json`. Against the previous build's checkpoint
[`97a501383083cc0fa64cb96405444048b8fd4053`](https://github.com/davidiach/adaptive-threshold-estimation/commit/97a501383083cc0fa64cb96405444048b8fd4053),
one TeX file is new (`appendix-sharp-rms.tex`) and six differ: `main.tex`,
`overview.tex`, `verification.tex` and the generated `core.tex`,
`introduction.tex` and `status-table.tex`. `status.json` differs in its
RMS-law entry. `sources.json` is the same at both checkpoints. The
manuscript workflow differs in one line, its push trigger, which is now
limited to `main`; its build steps are the same.

The sources pin one new revision,
[`f1425008ea71094d900b8cbb9a90b485f0884d33`](https://github.com/davidiach/adaptive-threshold-estimation/commit/f1425008ea71094d900b8cbb9a90b485f0884d33),
for their sixteen links to `lean/ThresholdHC/SharpRMS`. That commit added
the proofs to the library. Every other pinned source link is unchanged.

## How the PDF was built

The PDF comes from two local builds, not from a workflow artifact. Each
build ran in its own fresh copy of `paper/v6` at the source commit, with the
command and environment of the
[manuscript workflow](../../.github/workflows/manuscript.yml):

```sh
SOURCE_DATE_EPOCH=1793232000 FORCE_SOURCE_DATE=1 latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The two PDFs are byte-identical: 197 pages, 1,551,312 bytes, SHA-256
`f56c14c3ab41c4dd9714b97b919d4b685246999086fce4b5fcb1ea9e6a264f34`. The two
logs ([first](manuscript-build-1.log), [second](manuscript-build-2.log)) are
identical as well. The PDF has 33 embedded font objects, 421 unique source
labels and 29 resolved citations, and no unresolved or duplicate reference.
The only TeX warning is the inherited 5.16461 pt overfull line in
Appendix C.

[toolchain-validation.json](toolchain-validation.json) lists the TeX Live
packages, which come from the Ubuntu 24.04 archive as in the workflow. It
also records two checks of that toolchain, made for this build: it rebuilds
the two previous published PDFs byte for byte from their recorded source
commits. One of them,
[power-window-complete-20261116](../../paper/v6/builds/power-window-complete-20261116.pdf),
was published from a workflow build.

## Workflow build

The manuscript workflow runs on pull requests and on pushes to `main`.
[manuscript-ci.json](manuscript-ci.json) identifies one successful run,
for [#128](https://github.com/davidiach/adaptive-threshold-estimation/pull/128)
at the source commit. The job log reports 197 pages and a file size of
1,551,312 bytes, the size of the published PDF. Its only warning is the
same overfull line.

The workflow artifact was not downloaded, because the build session could
not reach GitHub's artifact storage. This record therefore does not claim
byte identity between the published PDF and a workflow artifact.

## Page comparison

[page-comparison.json](page-comparison.json) compares the PDF with the
previous build. Fourteen pages differ, as listed above. The two reference
pages are renumbered and otherwise identical. The other 181 pages retain
identical extracted body text and word positions. Every section and
subsection before Appendix AA starts on the page it started on.

The 14 changed pages, contents page 2 and the two reference pages were
rendered with Poppler at 100 dpi and visually inspected. No clipping,
overlap, missing text or displaced header or footer was found.

## An earlier build on the pull-request branch

A first build of this publication, `sharp-rms-constant-20261117` from
source commit `10de700`, existed only on the branch of
[#128](https://github.com/davidiach/adaptive-threshold-estimation/pull/128).
It typeset Appendix AA before the review above. This build and this record
replaced it before the pull request was merged, so it was never part of
`main`. Its files remain in the branch history, at commit `6f09ac0`.

## Scope

This record adds no Lean audit and no numerical experiment. The audit of
the sharp constant is in the [library audit record](../sharp-rms-20261117/README.md).
The proof evidence for every other claim of the manuscript is unchanged: it
is that of the [previous publication record](../review-corrections-publication-20261117/README.md)
and of the records in the [index](../README.md). The CI run named here built
the manuscript at its own commit; it is not evidence about a later commit.

[SHA256SUMS](SHA256SUMS) identifies the files of this record, the PDF and
the build record. All PDFs and records that reached `main` retain their
original bytes.
