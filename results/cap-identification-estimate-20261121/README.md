# Explicit fixed-cap estimate: library audit

The fixed-cap identification theorem of v6 Appendix `appendix-identifiability`
is Lean-checked as
[`fixed_cap_identification`](../../lean/ThresholdHC/CapIdentification/Full.lean):
attainment of the diameter $\Delta_N$, the limit $P_N(B)\to\Delta_N/2$, the
threshold $N\ge2m-1$ for $m$ atoms, and a positive floor for infinite support.
The proof also gives an explicit lower estimate on $\Delta_N$, which had a
paper proof only. Lean now checks it, in
[`lean/ThresholdHC/CapIdentificationEstimate`](../../lean/ThresholdHC/CapIdentificationEstimate/Full.lean).
The existing group and its sources are unchanged. The audit runs below were
made at commit
[`703d353`](https://github.com/davidiach/adaptive-threshold-estimation/commit/703d353).

## Statement

[`Specification.lean`](../../lean/ThresholdHC/CapIdentificationEstimate/Specification.lean)
states one target, `explicit_cap_estimate`. Let $\mu$ be a probability law of
gaps, $0<\rho\le1$ and $N\in\mathbb N$. Put $L=\lceil N/2\rceil$,
$\mathcal V_L=\operatorname{span}\{d,d^3,\ldots,d^{2L-1}\}\subset L^2(\mu)$ and
$h=1-\operatorname{proj}_{\mathcal V_L}1$. If $1\notin\mathcal V_L$, then $h\ne0$,
$\|h\|_{L^\infty(\mu)}$ is finite and positive, $\int h\,d^{2j+1}\,d\mu=0$ for
$j<L$, $\int h\,d\mu=\int h^2\,d\mu=\|h\|_{L^2(\mu)}^2>0$, and
$$\frac{\Delta_N}2\ge\frac{\rho\|h\|_{L^2(\mu)}^2}{4\|h\|_{L^\infty(\mu)}}.$$

$\Delta_N$ is `capDiameter`, the largest target gap between rare sign laws
whose odd moments up to $d^{2L-1}$ agree; it is defined as a supremum and
attained (`capDiameter_attained`). $\|h\|_{L^\infty(\mu)}$ is the
$\mu$-essential supremum. The paper's standing range is $0<\rho\le1/2$ and
$N\ge1$; the statement allows $\rho\le1$ and $N=0$, where $h=1$ and the bound
reads $\rho/4\le\rho/2$.

## How the proof goes

The proof is in [`Estimate.lean`](../../lean/ThresholdHC/CapIdentificationEstimate/Estimate.lean).
The residual $h$ is the $L^2(\mu)$ class of a polynomial, so it is bounded on
the gap interval and $M=\|h\|_{L^\infty(\mu)}$ is finite; it is nonzero
because $1\notin\mathcal V_L$. Orthogonality of the residual gives the
odd-moment identities and $\int h=\langle h,1\rangle=\langle h,h\rangle$. The
polynomial truncated at $\pm M$ agrees with $h$ almost everywhere and is
bounded by $M$, so
[`rare_priors_of_bounded_contrast`](../../lean/ThresholdHC/CapIdentification/RareContrast.lean)
gives the rare sign laws $\rho/2\pm(\rho/4M)h$. Their odd moments agree and
their target gap is $\rho\|h\|^2/(2M)$, which is at most $\Delta_N$. A separate
lemma, `exists_law_constant_not_mem`, shows that the hypothesis
$1\notin\mathcal V_L$ holds for the uniform law on $L+1$ distinct gaps.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_cap_identification_estimate.py --replay --jobs 3` | 4 exact statements (the target and 3 components) and 13 transitive axiom reports over the 3 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 3 modules replayed through the independent kernel checker. | [cap-identification-estimate-audit.log](cap-identification-estimate-audit.log) |
| `python -m unittest discover -s tools -p 'test_cap_identification_estimate.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,098 constants (13,731 theorems) in 1,469 modules, same axioms. 147 exported instances. 3,227 locked definition fingerprints. | [project-audit.log](../stopped-time-uniform-20261121/project-audit.log) of the stopped time-uniform record, the same run |
| `python tools/verify_lean_sources.py` | 1,470 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added seven
entries to `tools/definition_lock.json`: the three statements of
`StoppedTimeUniform`, the statement of `LatentThreshold`, the two statements of
`ZeroAtomSplit` and the statement of `CapIdentificationEstimate`. No existing
entry changed. The run recorded here is a later one without that flag; it
covers all four groups.

## Scope

This audit checks that the stated type is proved and which axioms the proof
uses. The specification was written after the proof; it is pinned by hash from
this audit onward. Sign laws are measurable $[0,1]$-valued functions with
$\int q\,d\mu\le\rho$, the model of the existing group, where the paper uses
$L^\infty(\mu)$ classes; the diameters agree.

## Review

Before the specification was pinned, a reviewer that had not written the proof
compared the statement with the paper's display: $\Delta_N$, $L=\lceil N/2\rceil$,
the odd-monomial span and the essential supremum all match, and the wider
ranges of $\rho$ and $N$ are harmless. It checked that the hypothesis is
satisfiable and that the conclusion gives a positive diameter for that law,
and found the proof sound. It found no blocking problem; its wording fix was
applied. This was a review by an AI agent, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
