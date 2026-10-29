# Revision 2: relation to the general-law characterization

These are the TeX sources of revision 2 of the [finite-gap manuscript](../README.md). Revision 1 in the parent directory, including its reviewed 32-page PDF, is unchanged and remains the published version.

> **PDF pending.** Revision 2 has not been compiled or visually inspected. Build it as below, inspect every page, then add `paper.pdf` and its hash to [SHA256SUMS](SHA256SUMS) before treating this revision as published.

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

Revision 2 is a paper proof, like revision 1. It is not Lean-checked and has not had external specialist review.

## Build and integrity

From this directory, with standard TeX Live or MiKTeX packages:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

Check the revision-2 sources with GNU coreutils:

```sh
sha256sum -c SHA256SUMS
```

Unchanged section files are byte-for-byte copies of revision 1, including the CRLF endings of three of them.
