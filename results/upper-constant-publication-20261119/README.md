# Publication of the RMS upper constant 15

The [205-page manuscript](../../paper/v6/builds/upper-constant-20261119.pdf)
typesets the v6 sources with the upper constant of the RMS law that Lean
already checked. With $\omega_\mu(h)=\int\min(1,h/d)\,\mu(dd)$:

- **Theorem AB.1.** For each $B\ge1$ there is one algorithm, depending only
  on $B$, that uses at most $B$ expected observations and has RMS error at
  most $15\,\omega_\mu(B^{-1/2})$ for every gap law $\mu$ and every sign
  law. In particular $R_\mu(B)\le15\,\omega_\mu(B^{-1/2})$, and with the
  sharp lower constant $1/6$ of Theorem AA.1 the two sides of the RMS law
  are within the factor $90$. Earlier builds stated $512$, which Section 18
  still records for the frozen target.

This record covers typesetting only. The proof evidence for the constant is
the [library audit record](../upper-sign-20261119/README.md) and the records
of the earlier stages that it extends.

## What changes in the text

| Location | Pages | Change |
|---|---|---|
| Contents | 2–3 | Appendix AB joins the group of Appendix AA, now "the constants of the RMS law". Sections 3, 4, 7 and 8 start one page later. |
| §1.1, Verification boundary | 5 | Coefficient $15$. |
| §1.2, overview table | 6 | The RMS row states $15$ and cites Theorem AB.1 and Appendix AB. |
| §1.3, status table | 8 | `UpperSign/Full.lean` joins the RMS-law row. |
| §1.4 | 10 | One sentence: Appendices AA and AB prove the constants $1/6$ and $15$. |
| Theorem 2.1 and its formal scope | 12 | $C=15$ for RMS; the formal scope cites `blind_upper_15` and `minimax_upper_15`. |
| §5.2 | 19 | One sentence pointing to Theorem AB.1. |
| §18 | 54, 58, 62–63 | The claim row of the RMS upper bound, a paragraph on the upper constant 15, and one sentence on Appendix AB. |
| Appendix AA.5 | 195 | The closing remark: the two sides are within the factor $90$. |
| Appendix AB | 198–203 | New: Theorem AB.1, Lemmas AB.2–AB.8 and their proofs, and what Lean checks. |
| References | 204–205 | Moved from pages 198–199, with no change. |

The other changed pages only reflow: pages 9, 11, 13–18 and 20–26 after the
edits of Sections 1, 2 and 5, and pages 55–57 and 59–61 in Section 18.
Section 18 still starts on page 54, and every appendix before AB starts on
its earlier page.

The status table keeps 33 entries: 32 Lean-checked and one paper proof.
`UpperSign/Full.lean` is added evidence for the existing RMS-law entry. The
results that use the distribution-blind family of Section 5 keep their
stated constants: the confidence bound of Theorem 2.1 and Appendices R, T
and Z. Appendix AB outlines the Lean proof and states which numerical
certificates Lean checks; it does not repeat them.

## Review of the new text

Lean checks the theorem. The written text is separate. Before this build, a
reviewer that had not written it read Appendix AB and the changed passages
of Sections 2, 5 and 18 against the Lean statements and recomputed every
constant in 40-digit arithmetic. It found no mathematical error. Its
findings:

- misattributed Lean modules: the proof also builds on `BlindUpper`,
  `UpperWork` and `UpperMoment`;
- a missing condition $K\ge0$ in the mixture lemma;
- a mismatch with the formal family for $B<4$, which outputs $0$;
- a numerical claim without a source;
- clashing symbols;
- wording that named `minimax_upper_15` for the family statement and
  credited the mixture alone.

Commit
[`1daed72`](https://github.com/davidiach/adaptive-threshold-estimation/commit/1daed723a678fc4417e57cc669abc55a39a30828)
fixes them. The reviewer also found that the results guide called the
constant of Section 5 larger than $512$; it is $\sqrt{8\cdot12666}<319$, and
the same commit corrects the guide. This was a review by an AI agent. It is
not a specialist referee report.

## Source identity

The TeX sources are pinned to
[`581444620f69ad9e169c07a43afd007d4b3612ae`](https://github.com/davidiach/adaptive-threshold-estimation/commit/581444620f69ad9e169c07a43afd007d4b3612ae).
The [build record](../../paper/v6/builds/upper-constant-20261119.json)
lists the SHA-256 of all 61 TeX files, of `status.json` and of
`sources.json`. The sources pin one new revision,
[`ac9e4ae6e8d8c266bab05140dacc6abfdaacb04d`](https://github.com/davidiach/adaptive-threshold-estimation/commit/ac9e4ae6e8d8c266bab05140dacc6abfdaacb04d),
the Lean commit of the upper constant 15, for their nine links to
`lean/ThresholdHC/UpperSign/Full.lean`, `UpperMixture/Full.lean` and
`UpperCost/Full.lean`.

## How the PDF was built

The PDF comes from two local builds, not from a workflow artifact. Each
build ran in its own fresh copy of `paper/v6` at the source commit, with the
command and environment of the
[manuscript workflow](../../.github/workflows/manuscript.yml):

```sh
SOURCE_DATE_EPOCH=1793232000 FORCE_SOURCE_DATE=1 latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The two PDFs are byte-identical: 205 pages, 1,608,201 bytes, SHA-256
`1abd807eb7353d4d6320680e554b0124381ca07806a683bf279b07d26725d6fb`. The two
logs ([first](manuscript-build-1.log), [second](manuscript-build-2.log)) are
identical as well. The PDF has 34 embedded font objects, 440 unique source
labels and 29 resolved citations, and no unresolved or duplicate reference.
The only TeX warning is the inherited 5.16461 pt overfull line in
Appendix C.

[toolchain-validation.json](toolchain-validation.json) lists the TeX Live
packages, which come from the Ubuntu 24.04 archive as in the workflow. The
same toolchain rebuilds the four previous published PDFs byte for byte from
their recorded source commits; the rebuilds were made for this build. The
earliest of them,
[power-window-complete-20261116](../../paper/v6/builds/power-window-complete-20261116.pdf),
was published from a workflow build.

## Workflow build

[manuscript-ci.json](manuscript-ci.json) identifies one successful run of
the manuscript workflow, for
[#145](https://github.com/davidiach/adaptive-threshold-estimation/pull/145)
at the source commit. Its job log reports 205 pages and a file size of
1,608,201 bytes, the size of the published PDF. Its only warning in the
final pass is the same overfull line. The workflow artifact was not
downloaded, because the build session could not reach GitHub's artifact
storage, so this record does not claim byte identity with it.

## Page comparison

[page-comparison.json](page-comparison.json) compares the PDF with the
previous build, `large-budget-bracket-20261118`, by rendered pixels: each
page at 100 dpi in grey, with a 60 pt band at the top and the bottom left
out for the running header and the page number. Earlier records compared
the word boxes that `pdftotext` reports. Those boxes move on every page
here, because the new glyphs change the embedded font subsets and with them
the font metrics that `pdftotext` uses, so they no longer separate changed
pages from unchanged ones. A page counts as unchanged only if its body
pixels are identical.

Forty pages differ, as listed above. The two reference pages are renumbered
and otherwise identical. The other 163 pages have identical body pixels.
The 40 changed pages and the two reference pages were rendered with Poppler
at 100 dpi and visually inspected, in contact sheets of four pages. No
clipping, overlap, missing text or displaced header or footer was found.

## Scope

This record adds no Lean audit and no numerical experiment. The proof
evidence for every other claim of the manuscript is unchanged: it is that
of the [previous publication record](../large-budget-publication-20261118/README.md)
and of the records in the [index](../README.md). The CI run named here built
the manuscript at its own commit; it is not evidence about a later commit.

[SHA256SUMS](SHA256SUMS) identifies the files of this record, the PDF and
the build record. All PDFs and records that reached `main` retain their
original bytes.
