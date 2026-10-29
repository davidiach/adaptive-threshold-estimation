# Revision 2: relation to the general-law characterization

[Read the 35-page PDF](paper.pdf) · [Build and integrity](#build-and-integrity)

This is revision 2 of the [finite-gap manuscript](../README.md). Revision 1 in the parent directory, including its reviewed 32-page PDF, is unchanged.

## What changed

Revision 2 adds Section 7 ([`sections/comparison.tex`](sections/comparison.tex)) and leaves every existing result, proof and label unchanged. Section 7 compares the closed functional $Q$ with the selection functional $\mathcal K$ of the companion [general-law manuscript](../../rare-event/README.md), which optimizes over submeasures of $\mu$:

```math
\mathcal K(B)\le Q(B)\le(1+2\sqrt2)\,\mathcal K(B)<4\,\mathcal K(B)
```

for every probability law on $(0,1/2]$, every $0<\rho\le1/4$ and every $B>0$, with $\mathcal K=Q=\rho$ once $h=B^{-1/2}$ reaches the quantile boundary. The comparison is deterministic and uses neither statistical theorem. Consequences:

- **Finite laws.** With Theorem 1.1, $10^{-20}\mathcal K\le R\le30001(1+2\sqrt2)\mathcal K$. This is the finite-law case of the companion characterization, proved here without invoking its theorem.
- **The converse route.** The companion theorem, if granted, gives $R\asymp Q$ for finite laws with constants $10^{-17}/(1+2\sqrt2)$ and $33000$: a better lower constant than $10^{-20}$ and a slightly worse upper one than $30001$.
- **General laws, conditionally.** If the companion theorem holds, $R\asymp Q$ holds for every law on $(0,1/2]$. This is not a result of the manuscript; it rests entirely on the companion theorem.
- **Not independent evidence.** Both manuscripts grew from the same research notes. They share the observable upper construction and most appendix lemmas, and differ mainly in the lower-bound reduction. The two results are one rate established by two arguments, not two independent confirmations.

The other changes are:
- a paragraph in §2.2 distinguishing the result from Aronow, Kallus and Lopatto's [resolution of the gap-entropy conjecture](https://arxiv.org/abs/2609.10529v1) for Gaussian best-arm identification;
- a paragraph in §2.2 stating the dependency on the companion manuscript;
- one sentence in the abstract, pointers in §2.1 and §6, a revision line under the date, and two bibliography entries.

## Provenance and checks

Approved by the project owner in chat ("separate change, yeah"), after an external adversarial review (Astra Pro) of revision 1 at commit `2984835`. That review supplied the comparison, with a proof over hard selections. Section 7 proves it directly for the companion's selection over submeasures, which also makes the lower comparison immediate, and cites the paper's existing mixture bound from §2.3 instead of re-proving it.

Checks of revision 2:
- The proof was checked step by step against the definitions of both manuscripts.
- An adversarial review covered the mathematics, framing and numerics:
  - An independent implementation checked 700,000 law, rarity and budget cases over 100,000 random finite laws, including fractional boundary atoms and $h$ at, below and above the quantile boundary, plus 4,099 cases rechecked at 60 digits. It found no violation.
  - No soft selection beat the hard minimum.
  - An adversarial search found $Q/\mathcal K$ approaching about 1.461, so the constant $1+2\sqrt2$ is valid but loose.
  - Only finite atomic laws were tested numerically.
- The sources pass static LaTeX checks: environments, braces, 97 unique labels, and every reference and all eight citations resolve.
- The PDF builds without LaTeX warnings, undefined references or overfull boxes, and all its fonts are embedded. All 35 pages were visually inspected.
- That inspection found seven minor issues in the new material, all fixed before the PDF was committed:
  - the §2.2 paragraph structure;
  - the Aronow–Kallus–Lopatto sum, now over suboptimal arms only;
  - a missing caveat that the companion's proof is unrefereed;
  - notation in the proof of Lemma 7.1;
  - spacing at the end of the proof of Proposition 7.2;
  - the bibliography's label width and order.
- The text was compared word by word with revision 1 built by the same engine. The only differences are the additions listed above, page numbers after §6 and equation numbers in the appendices. Revision 1's citation numbers are kept; the new entries are [7] and [8].

Revision 2 is a paper proof, like revision 1. It is not Lean-checked and has not had external specialist review.

## Build and integrity

From this directory, with standard TeX Live or MiKTeX packages:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The committed `paper.pdf` was built this way with pdfTeX 1.40.25 (TeX Live 2023, Ubuntu 24.04 packages) and a fixed source date:

```sh
SOURCE_DATE_EPOCH=1793232000 FORCE_SOURCE_DATE=1 latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

With that engine the build reproduces `paper.pdf` byte for byte; another engine or TeX Live release may differ in bytes. Revision 1's PDF was exported with Tectonic instead; built with the same pdfTeX, its sources also give 32 pages.

Check the revision-2 sources with GNU coreutils:

```sh
sha256sum -c SHA256SUMS
```

Unchanged section files are byte-for-byte copies of revision 1, including the CRLF endings of three of them.
