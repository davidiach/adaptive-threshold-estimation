# Consolidated version 6

[Read the manuscript](paper.pdf) · [Open the LaTeX project](main.tex) · [Build record](#build-record)

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

## Verification status

Lean checks both directions of the original RMS law, the critical quadratic
law, the exact Ψ comparison and counterexample, the variational optimizer,
the unbiased characterization with constants 1/16 and 713, the confidence
characterization, the magnitude-oracle lower bounds, and the rare-event
rate above exponent two. It also checks the upper half of the entropy–tail
law, the closed quantile upper bound for every law, the comparison
$K\le Q\le(1+2\sqrt2)K$, and the stopping-program, fixed-cap
identification and genie results of §15, each in the scope stated in §18.
Section 18 states each formal scope and links the fixed source revisions.

The lower half of the entropy–tail law, and hence the two-sided law and the
two-sided closed quantile form (including its direct proof for finite laws),
and the rare-event regimes below two are **paper proofs**. They are not
Lean-formalized and have not had external specialist review. The general-law and finite-gap proofs share
their upper construction and Appendices F–H, so they are one rate
established by two arguments, not two independent confirmations. The remark
in §11 on agreement of the power-margin table with the closed quantile form is
new in this edition; it is a consistency check, not additional verification.

## Source and editorial scope

[build_v6.py](../../tools/build_v6.py) generates 28 of the TeX files from the
inputs hash-locked in [sources.json](sources.json): the v5 project files,
the general-law v2 sections and bibliography, and the finite-gap revision 2
sections. The editable exposition is in `frontmatter.tex`, `rare-events.tex`,
`entropy-tail.tex`, `finite-laws.tex`, `certificates.tex`,
`finite-proof.tex` and `verification.tex`; `main.tex` controls the layout.
Do not edit the generated files directly.

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
  `8fb16244ded0d6cebf4ba78e1ad9adae09ef293d`.

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

## Build record

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
