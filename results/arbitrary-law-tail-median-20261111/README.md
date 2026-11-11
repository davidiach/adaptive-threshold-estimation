# The median tail certificate

This record covers the amplification step of the
[inverse-sampling procedure](../../docs/ARBITRARY_LAW_TAIL.md#inverse-sampling-under-a-physical-budget)
of the arbitrary-law tail certificate. `m` copies of the
[capped tail probe](../arbitrary-law-tail-probe-20261110/README.md) at depth
$J$ run on separate streams of fresh coins. The certificate $U$ is the median
of their certificates: the entry of rank $\lfloor m/2\rfloor$ in increasing
order.

Write $t=2^{-J}$, $F(t)=\mu((0,t])$, $u_J$ for the unresolved probability of
one coin, and $W_J=\int w_J\,d\mu$. The statements hold for every probability
law $\mu$ of positive gaps and every measurable gap-dependent sign law $q$.

| Statement | Lean-checked guarantee |
|---|---|
| [Median](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailMedian.lean) | If more than half of `m` values are at least `a`, so is the median, and if more than half are at most `c`, so is the median. The median certificate lies in $(0,1]$. |
| [Flip cap](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailMedian.lean) | With a common flip budget $b$ the `m` probes are charged at most $mb$ flips on every stream. |
| [Hoeffding across probes](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailMedianProbability.lean) | Along independent blocks, a set of probability at least $3/4$ contains more than half of the first `m` blocks, except with probability $e^{-m/8}$. |
| [Calibration](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailMedianProbability.lean) | $2e^{-m/8}\le\delta$ when $m\ge8\log(2/\delta)$, and $\sum_{J<n}\delta/(J(J+1))\le\delta$ for every $n$. |
| [Statement (1)](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailMedianLaw.lean) | For $m\ge8\log(2/\delta)$ probes with flip budget $4^J$ each, with probability at least $1-\delta$, $F(t)\le U\le\min\{1,128\max(u_J,W_J/4^J)\}$. The lower bound holds for every choice of the probes' flip budgets and coin caps. |
| [With a coin cap](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailMedianLaw.lean) | With a common budget $b\ge1$ and coin cap $M\ge1$, the upper bound is $\min\{1,128\max(u_J,W_J/b,1/M)\}$, and both bounds fail with probability at most $2e^{-m/8}$. |
| [Every depth](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailMedianLaw.lean) | With $m_J\ge8\log(2J(J+1)/\delta)$ probes at depth $J$ on its own streams, both bounds hold at every depth $J\ge1$ at once with probability at least $1-\delta$. |
| [One coin array](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailMedianLaw.lean) | Splitting a sequence of independent coins by the pairing function gives independent streams. Statement (1) and the every-depth statement hold on the coin array of the original simulation law, where probe $j$ of depth $J$ reads the coins `Nat.pair J (Nat.pair j i)`. |

The amplification does not use the binomial law of the number of failing
probes directly. Along independent blocks the indicators of a set form a
Bernoulli tape, so the project's existing
[Hoeffding bound for tape prefixes](../../lean/ThresholdHC/EntropyTailUpper/PrefixConcentration.lean)
applies. A probe fails coverage with probability at most $1/8$ and fails the
performance bound with probability at most $1/4$; either way at least half of
the probes fail with probability at most $e^{-m/8}$. The two failure events of
the median are joined by a union bound and are not assumed independent.
Because the lower bound holds for every choice of the probes' budgets, it
covers a procedure that is stopped part of the way through, with some probes
complete, one interrupted and the rest not started.

This is the median and the union over depths. It does not include:

- The oracle comparison (3), its lowest-gap quantile decomposition and its
  onset.
- The pilot of (A6) to (A8) in the
  [adaptation proof](../../docs/ARBITRARY_LAW_ADAPTATION.md), which uses a
  common number of probes, the caps $b_j$ and $M$, and a finite union over
  depths.
- Readers in the observable stage. The probes are defined on streams of tapes.
  The single-array statements fix which coins each probe reads; they do not
  construct the policy that reads them.
- The arbitrary-law adaptation theorem, which remains a paper proof.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/fedb0dc172f9c6eb537154ba3fe524dbfaabd1f2),
the three new modules were built from source on Linux with Lean
`v4.36.0-rc1`, on top of a build of every project module made in the same
environment and against the Mathlib cache for the pinned revision. They
compiled without warnings. [51 exact statements](arbitrary_law_tail_median.lean)
passed with [51 transitive axiom reports](arbitrary_law_tail_median.log), one
for each declaration of the three modules, using only `propext`,
`Classical.choice` and `Quot.sound`. The whole-project audit
`python tools/verify_project_axioms.py --no-build` passed on the same build:
1,161 modules, 11,954 constants and 9,646 theorems, with no declared axiom. Its
kernel replay was not run locally. The [native record](status.json) lists the
source hash of every project module in the import closure of the new
modules. Its base checkpoint is the head of the tail-probe change.

Two checks outside Lean were run during review and are supporting evidence
only. A literal transcription of the median agreed with the
[toolkit](../../toolkit/threshold_toolkit/tail_mass.py) on 300 replayed runs,
and the toolkit's block counts satisfy $m\ge8\log(2/\delta)$. A Monte Carlo
run for one gap law found coverage failures far below $e^{-m/8}$.

Run `python tools/verify_arbitrary_law_tail_median.py` with the pinned
toolchain. The audit restates every definition and theorem in full and fails
if a declaration of the three modules is not registered.
