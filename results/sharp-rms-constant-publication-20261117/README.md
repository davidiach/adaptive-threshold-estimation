# Publication of the sharp RMS constant

The [197-page manuscript](../../paper/v6/builds/sharp-rms-constant-20261117.pdf)
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
| Abstract | 1 | The RMS law has coefficients $1/6$ (sharp) and $512$. The date is 17 November 2026. |
| Contents | 3 | A part heading and an entry for Appendix AA. |
| §1.1, verification boundary | 5 | Coefficients $1/6$ and $512$. |
| §1.2, overview table | 6 | The RMS-law row states $1/6$, says that it is sharp and cites Theorem AA.1. |
| §1.3, status table | 8 | The RMS-law row states $1/6$ (sharp) and lists `SharpRMS/Full.lean`. |
| Theorem 2.1 | 12 | One may take $c=1/6$ for RMS, which is sharp. The formal scope names the Lean theorem `sharp_lower`. |
| §18 | 62–63 | One sentence on the audit of Appendix AA. It adds three lines, so two lines move to page 63. |
| Appendix AA | 191–195 | New: the proof of the sharp constant, also under both magnitude oracles. |
| References | 196–197 | Moved from pages 191–192, with no change. |

The status table keeps 33 entries: 32 Lean-checked and one paper proof. The
sharp constant is added evidence for the existing RMS-law entry. §5 still
proves $1/64$, the coefficient of the frozen lower-bound target. The upper
constant $512$ is unchanged.

## Source identity

The TeX sources are pinned to
[`10de700fd72eaa474f20bd0bbfcca21ddf85c301`](https://github.com/davidiach/adaptive-threshold-estimation/commit/10de700fd72eaa474f20bd0bbfcca21ddf85c301).
The [build record](../../paper/v6/builds/sharp-rms-constant-20261117.json)
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

The two PDFs are byte-identical: 197 pages, 1,549,771 bytes, SHA-256
`63fc6c138526c7ef1d83c407150473bc3b28fe57f980a378428a7db28eab5464`. The two
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

No workflow build is cited. The manuscript workflow now runs on pull
requests and on pushes to `main`, so the source commit has no push build.
The first pull-request build of these sources, run
[44196014649](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/44196014649)
for [#128](https://github.com/davidiach/adaptive-threshold-estimation/pull/128)
at head `3cff4fe`, had not finished when this record was written.

The published PDF therefore rests on the two local builds. Its link to the
workflow is the toolchain check above: the same packages and command
reproduce a PDF that the workflow built.

## Page comparison

[page-comparison.json](page-comparison.json) compares the PDF with the
previous build. Thirteen pages differ, as listed above. The two reference
pages are renumbered and otherwise identical. The other 182 pages retain
identical extracted body text and word positions. Every section and
subsection before Appendix AA starts on the page it started on.

The 13 changed pages, contents page 2 and the two reference pages were
rendered with Poppler at 100 dpi and visually inspected. No clipping,
overlap, missing text or displaced header or footer was found.

## Scope

This record adds no Lean audit and no numerical experiment. The audit of
the sharp constant is in the [library audit record](../sharp-rms-20261117/README.md).
The proof evidence for every other claim of the manuscript is unchanged: it
is that of the [previous publication record](../review-corrections-publication-20261117/README.md)
and of the records in the [index](../README.md).

[SHA256SUMS](SHA256SUMS) identifies the files of this record, the PDF and
the build record. All earlier PDFs and records retain their original bytes.
