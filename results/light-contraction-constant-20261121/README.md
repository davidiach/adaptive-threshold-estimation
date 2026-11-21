# The constant of the light random contraction: library audit

The arbitrary-law adaptation section of the v6 paper
([`paper/v6/arbitrary-law-adaptation.tex`](../../paper/v6/arbitrary-law-adaptation.tex),
paragraph *A light random contraction*, display (UA4); display (A4) of
[`docs/ARBITRARY_LAW_ADAPTATION.md`](../../docs/ARBITRARY_LAW_ADAPTATION.md))
takes a multiplier $V$ with distribution function
$G_V(v)=2e^{-1/(2v^2)}$ on $(0,1/4)$ and $G_V=1$ from $1/4$ on, writes
$p_k=\Pr(2^{-k-1}<V\le2^{-k})$ for $k\ge2$, and states

$$p_2=1-2e^{-32},\qquad p_k\le2e^{-4^k/2}\ (k\ge3),\qquad
C_V=\sum_{k\ge2}4^{k+1}p_k\bigl[1+\log(1/p_k)+\log2\bigr]<256,$$

with a first summand below $192$, $\mathbb EV^{-2}\le C_V\le256$ and
$\mathbb EV^{-1}\le16$. The checked factor-32 comparison
([light-contraction record](../arbitrary-law-light-20261106/README.md)) uses
a different reference code, and the guides list the series bound as a paper
calculation. Lean now checks these constants, in
[`lean/ThresholdHC/LightContractionConstant`](../../lean/ThresholdHC/LightContractionConstant/Full.lean).
The `ArbitraryLawAdaptation` group and the paper are unchanged. The audit
runs below were made at commit
[`c9f5800`](https://github.com/davidiach/adaptive-threshold-estimation/commit/c9f5800).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/LightContractionConstant/Specification.lean)
defines the band mass `bandProb ν k`, the summand `cvTerm ν k` and
`lightCV ν`, the series indexed from $k=2$, and states six targets for every
probability law $\nu$ on gaps whose distribution function is the existing
`lightCDF`, and for the constructed multiplier `lightMultiplier`.

| Target | Statement |
|---|---|
| `first_band_mass` | $p_2=1-2e^{-32}$. |
| `tail_band_mass` | $p_k\le2e^{-4^k/2}$ for every $k\ge3$. |
| `first_term_bound` | The $k=2$ summand of $C_V$ is less than $192$. |
| `light_cv_bound` | The series converges and $C_V<256$. |
| `light_moment_bounds` | $\mathbb EV^{-2}\le C_V$, $\mathbb EV^{-2}\le256$ and $\mathbb EV^{-1}\le16$, as lower Lebesgue integrals. |
| `constructed_light_cv` | For `lightMultiplier`: $p_2=1-2e^{-32}$, the series converges and $C_V<256$. |

Lean's conventions $\log0=0$ and $1/0=0$ apply; every $p_k$ lies in $[0,1]$,
and the summability conjunct rules out the value $0$ that a divergent
`tsum` would take. The first-summand bound holds for every probability law;
its distribution-function premise is not used. The entropy inequality
$\Gamma_{\mathcal L(VD)}\le C_V\Gamma_\mu$ of (UA4) is not stated.

## How the proofs go

- [`Masses.lean`](../../lean/ThresholdHC/LightContractionConstant/Masses.lean)
  evaluates the band masses from the distribution function.
- [`Series.lean`](../../lean/ThresholdHC/LightContractionConstant/Series.lean)
  bounds the first summand by $64(1+\log2)<128$ through
  $p\log(1/p)\le1-p$, where the paper uses $1/e$, and each later summand by
  $12\cdot16^{-n}$ through the checked exponential-cost bound
  ($e^x\ge x^4/24$, as in the paper). Every summand is then at most
  $192\cdot16^{-j}$, which gives summability and the sharper
  $C_V\le1024/5=204.8$.
- [`Moments.lean`](../../lean/ThresholdHC/LightContractionConstant/Moments.lean)
  compares the inverse moments with the band sums.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_light_contraction_constant.py --replay --jobs 3` | 9 exact statements (the 6 targets and 3 components) and 42 transitive axiom reports over the 5 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 5 modules replayed through the independent kernel checker. | [light-contraction-constant-audit.log](light-contraction-constant-audit.log) |
| `python -m unittest discover -s tools -p 'test_light_contraction_constant.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 18,262 constants (14,700 theorems) in 1,558 modules, same axioms. 151 exported instances; 6 registered orphans, unchanged. 3,421 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,559 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added nine
entries to `tools/definition_lock.json`: `bandProb`, `cvTerm`, `lightCV` and
the six statements. No existing entry changed. The run recorded here is a
later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. The entropy inequality of (UA4), with $C_V$ as
its factor, stays a paper calculation; the final theorem does not need it,
since the checked factor-32 comparison uses its own reference code. The
earlier light-contraction record describes its own checkpoint and is
unchanged.

## Review

The item was planned by one agent, criticized by a second, which added the
bound $\mathbb EV^{-2}\le256$, relabelled the constant's statement and named
two proof fixes, and written by a third. Before the specification was
pinned, a fourth agent that had not written the proofs rebuilt the modules,
restated the targets with the distribution function and band masses
unfolded, printed the axioms of all 42 public declarations, ran the audit's
scans and probed non-vacuity: the constructed multiplier meets the premise,
$p_2>0$, and the first summand is at most the series value, so the sum is
not the conventional $0$. It found three minor points: one docstring claimed
$C_V\le256$ in a statement that does not contain it, another overstated what
the constructed-multiplier statement covers, and the module header gave the
wrong sectioning levels. All three were reworded before this audit. These
were reviews by AI agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
