# Adaptive estimation of rare signs with a known finite gap law

[Paper (32-page PDF)](paper.pdf) · [LaTeX entry point](main.tex) · [Provenance](PROVENANCE.md) · [File hashes](SHA256SUMS)

Standalone manuscript dated 29 October 2026, prepared for external mathematical review. The exact theorem is Theorem 1.1 on page 2. All specialized ingredients have proofs in the paper; no unpublished selection theorem or earlier working note is needed to read it.

## Theorem and assumptions

For a known law $\mu=\sum_{i=1}^n w_i\delta_{d_i}$ with $n<\infty$, positive weights and $0<d_i\le1/2$, known rarity $0<\rho\le1/4$, and budget $B>0$,

```math
10^{-20}Q(B)\le R_{\mu,\rho}(B)\le30001Q(B),\qquad
Q(B)=\min\{\rho,T_h+h\sqrt{\rho\Gamma_\kappa}\},\quad h=B^{-1/2}.
```

Remove exactly the smallest-gap mass $\rho$ into $\nu$, splitting a boundary atom when necessary, and put $\kappa=\mu-\nu$. Then

```math
T_h=\int\min(1,h/d)\,\nu(dd),\quad
I_j=(2^{-j-2},2^{-j-1}],\quad
a_j=\int_{I_j}d^{-2}\,\kappa(dd),\quad A=\sum_j a_j,
```

```math
\Gamma_\kappa=A+\sum_{j:a_j>0}a_j\log(A/a_j),\qquad j=0,1,2,\ldots.
```

The statistical and budget assumptions are:

- The unknown function $q$ satisfies $0\le q\le1$ and the **global** rarity constraint $\theta(q)=\int q\,d\mu\le\rho$.
- Fresh coins have iid complete latent pairs $(D,S)$, with $D\sim\mu$ and $\Pr(S=+1\mid D=d)=q(d)$. Each pair persists on revisits. Conditional on the pairs, independent tapes contain iid Bernoulli$(1/2+SD)$ observations.
- The algorithm observes coin identities, its independent seed and purchased flips. It may create, revisit and interleave coins. Neither genuine gaps nor signs are revealed.
- The risk is worst-case RMS error in estimating $\theta(q)$. The budget is $\sup_q\mathbb E_qN\le B$, counting every physical observation. Creation, computation and random-number generation are not charged.
- One upper procedure is chosen for each known $(\mu,\rho,B)$ and works for every admissible $q$. The lower bound covers every algorithm satisfying that same uniform budget, including nonlinear outputs and unbounded stopping.

The constants are deliberately loose. The theorem is a comparison up to universal constants; it does not cover unknown gap laws, general infinite supports, deterministic total budgets or high-confidence guarantees.

## Proof and review status

This is a **paper proof, not a Lean-checked theorem**. The repository's formal results concerning unrestricted sign laws, the critical quadratic law or finite-gap sign entropy do not verify this closed quantile characterization.

The precursor complete proof passed a fresh-context AI review using the inherited model. The standalone version was checked for preservation of proof content, compilation, cross-references and page layout. It has not received external human specialist review or proof-assistant verification. Numerical diagnostics are not used as proof certificates. The [provenance note](PROVENANCE.md) records the scope of the checks.

## Reading guide

| Location | Contents |
|---|---|
| §§1–2, pages 1–4 | Model, exact theorem, quantifiers, testing conventions, proof roadmap and entropy preliminaries |
| §3, pages 4–8 | Posterior tail obstruction, entropy filter and feasible packing |
| §4, pages 8–12 | Observable classifier race, finite multilevel allocation and work bounds |
| §5, pages 12–13 | Final assembly and explicit universal constants |
| §6, pages 13–14 | Mean-square and one-gap corollaries with proofs |
| Appendix A, pages 15–19 | Classification, likelihood bank, race and Poisson allocation |
| Appendix B, pages 20–25 | Weighted sign entropy, activation gate and annular lower bound |
| Appendix C, pages 26–31 | Convex comparison, common pairs, adaptive transfer and localization |
| Page 32 | Public bibliography |

## Build and integrity

From this directory, with standard TeX Live or MiKTeX packages:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

Alternatively run `pdflatex main.tex` twice, or `tectonic main.tex`. The source uses no shell escape, external figures, custom classes or BibTeX database. Build output is `main.pdf`; the reviewed, checked-in PDF is `paper.pdf`. Generated intermediates are ignored. The repository copy preserves the reviewed PDF bytes and TeX content, with only trailing whitespace and terminal blank lines normalized in three source files.

The committed PDF was exported with Tectonic 0.17.0 and the source also compiled with the Codex built-in compiler. All 32 pages were visually inspected, all 21 fonts are embedded, and all 91 LaTeX labels and the six public bibliography entries resolve. These are document checks, not mathematical certification. A fresh build may differ in PDF metadata or bytes across engines.

Check the committed file hashes with GNU coreutils:

```sh
sha256sum -c SHA256SUMS
```

The author line is blank in the supplied manuscript. Responsible authors should provide the desired authorship and venue-specific AI-assistance disclosure before submission. The paper, TeX sources and documentation follow the repository's [CC BY 4.0 license](../../LICENSE-CC-BY-4.0) and [attribution policy](../../LICENSES.md).
