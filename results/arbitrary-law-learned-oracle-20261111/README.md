# The learned law retains the oracle rate

This record covers the second part of the learned law's oracle comparison in
the [arbitrary-law adaptation proof](../../docs/ARBITRARY_LAW_ADAPTATION.md#3-the-learned-law-retains-the-oracle-rate):
the learned-CDF bound (A13), the slack bound (A14), the clipped-CDF witness,
and the comparison (A11). The first part is the record of the
[work estimates and onset](../arbitrary-law-pilot-onset-20261111/README.md).

Fix $0<\rho\le1/4$ and a probability law $\mu$ of positive gaps. For the
[pilot](../arbitrary-law-pilot-20261111/README.md) of target depth $J\ge1$
write $N=4^J$, $b_j$ for the flip budget of depth $j$ and $M$ for the coin
cap. $u_j$ is the unresolved probability of one coin at depth $j$ and
$W_j=\int w_j\,d\mu$. As in the first part, $\nu$ is the lowest-gap quantile
part of $\mu$ of mass $\rho$, $a$ is its threshold and
$\tau_\nu(s)=\int\min\{1,s/d\}\,d\nu$. $U_1=1$ and $U_2,\dots,U_J\ge0$ are
certificates, $c_j=\min_{i\le j}U_i$, and $\bar\mu$ is the learned law (A9)
with distribution function $F_{\bar\mu}$. The upper half of (A8) is
$U_j\le128\,(u_j+W_j/b_j+1/M)$ at every depth $1\le j\le J$.
$K_{\mu,\rho}(N)$ is the
[entropy-tail selection functional](../../lean/ThresholdHC/EntropyTail/Model.lean),
and $K_{\bar\mu,\rho}(N)$ is its
[extension to laws with mass at zero](../../lean/ThresholdHC/ArbitraryLawAdaptation/ZeroModel.lean),
which keeps the infimum over all fractional selections.

| Statement | Lean-checked guarantee |
|---|---|
| [Multiplier law](../../lean/ThresholdHC/ArbitraryLawAdaptation/LearnedCDF.lean) | $\mu'=\mathcal L(VD/2)$, with $D\sim\mu$ and $V$ the independent light multiplier of the [contraction](../arbitrary-law-light-20261106/README.md). The unresolved probability of one coin at depth $j$ satisfies $u_j\le F_{\mu'}(2^{-(j+1)})$. |
| [(A13)](../../lean/ThresholdHC/ArbitraryLawAdaptation/LearnedCDF.lean) | Under the upper half of (A8), at every real $x$: $F_{\bar\mu}(x)\le\min\{1,128F_{\mu'}(x)+e\}$ with $e=128w+128/M+c_J$, where $w=8192\,\tau_\nu(2^{-J})+2048(J+1)^3 4^{-J}/a^2$ bounds $W_j/b_j$ at every depth. No onset is needed, and $\rho\le1$ suffices. |
| [(A14)](../../lean/ThresholdHC/ArbitraryLawAdaptation/LearnedCDF.lean) | Under the pilot's onset condition, $w\le8193\,K_{\mu,\rho}(N)$, and when $U_J$ satisfies the upper half of (A8), $e\le2621712\,K_{\mu,\rho}(N)$. There $K_{\mu,\rho}(N)$ is positive and finite, so $e<2^{22}K_{\mu,\rho}(N)$. |
| [Quantile part](../../lean/ThresholdHC/ArbitraryLawAdaptation/LearnedOracle.lean) | For $0<r\le1$, the lowest-gap quantile part of mass $r$ of a law $\eta$ has distribution function $\min\{r,F_\eta\}$. |
| [Witness](../../lean/ThresholdHC/ArbitraryLawAdaptation/LearnedOracle.lean) | For a law $\eta$ of positive gaps and $e\ge0$, $\lambda$ is $\delta_0$ when $e\ge1$, and otherwise $e\,\delta_0$ plus $128$ times the quantile part of $\eta$ of mass $(1-e)/128$. It is a probability law, $\lambda\le128\eta+e\,\delta_0$, it has no mass below zero, and $F_\lambda(x)=\min\{1,128F_\eta(x)+e\}$ for every $x\ge0$. |
| [(A11)](../../lean/ThresholdHC/ArbitraryLawAdaptation/LearnedOracle.lean) | Under the pilot's onset condition and the upper half of (A8): $K_{\bar\mu,\rho}(N)\le2^{24}K_{\mu,\rho}(N)$. |
| [Onset](../../lean/ThresholdHC/ArbitraryLawAdaptation/LearnedOracle.lean) | There is a depth $J_0\ge1$, depending on $\mu$ and $\rho$ only, such that (A11) holds at every $J\ge J_0$ for all certificates that satisfy the upper half of (A8). |
| [On the pilot event](../../lean/ThresholdHC/ArbitraryLawAdaptation/LearnedOracle.lean) | For the pilot in the paid learning stage with $m\ge8\log(2J/\varepsilon)$ probes at every depth, under the onset condition: with probability at least $1-\varepsilon$ on the coin array of the original simulation law, the stage's learned law dominates $\mu$ in distribution and satisfies (A11). This holds for every $J\ge J_0$, every measurable gap-dependent sign law and every stage. |

The comparison is the chain
$K_{\bar\mu}\le\sqrt3\,K_\lambda\le2\,(128K_{\mu'}+e)\le2\,(4096+2^{22})K_\mu$,
with $\eta=\mu'$ in the witness. Its steps are the existing
[CDF comparison](../arbitrary-law-zero-cdf-20261106/README.md),
[dominated-mass bound](../arbitrary-law-dominated-20261106/README.md) and
[light contraction](../arbitrary-law-light-20261106/README.md),
and (A14). The bound on $u_j$ is the existing
[terminal estimate of the tail test](../arbitrary-law-tail-test-20261110/README.md).

(A13) is stated with the depth-independent bound $w$ in place of the paper's
$\max_jW_j/b_j$; (A12) bounds each $W_j/b_j$ by $w$. $V$, $\mu'$, $\lambda$,
$e$, the threshold $a$ and the onset are proof quantities. The pilot neither
samples nor computes them, and the learned law is computed from the
certificates read off the observed word.

The range $\rho\le1/4$ comes from the
[oracle comparison of the tail certificate](../arbitrary-law-tail-oracle-20261111/README.md).
The onset is the one of the first part, which is large: for a point mass at
$1/2$ and $\rho=1/4$ it first holds at depth 29.

This completes (A11) to (A14). It does not include:

- The event stated under the law of the experiment of the whole stage. It is
  stated on the coin array of the original simulation law, as (A8) is.
- The robust continuation that uses the learned law, the all-budget
  controller and the arbitrary-law adaptation theorem, which remains a paper
  proof.
- Python execution of the toolkit.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/98dbe58826ee1d57fb77a47c9443b3ed22ac1fc6),
the two new modules were built from source on Linux with Lean `v4.36.0-rc1`,
on top of a build of every project module made in the same environment and
against the Mathlib cache for the pinned revision. They compiled without
warnings. [31 exact statements](arbitrary_law_learned_oracle.lean) passed with
[31 transitive axiom reports](arbitrary_law_learned_oracle.log), one for each
declaration of the two modules, using only `propext`, `Classical.choice` and
`Quot.sound`. The whole-project audit
`python tools/verify_project_axioms.py --no-build` passed on the same build:
1,171 modules, 12,324 constants and 9,948 theorems, with no declared axiom. Its
kernel replay was not run locally. The [native record](status.json) lists the
source hash of every project module in the import closure of the new
modules. Its base checkpoint is the head of the work-estimates change.

One check outside Lean was run during review and is supporting evidence only.
A literal transcription of the quantile part and of the witness, in exact
rational arithmetic, was run on 4,000 random discrete laws with $e$ on both
sides of 1: the witness had unit mass, was dominated by $128\eta+e\,\delta_0$
atom by atom, and its distribution function equalled $\min\{1,128F_\eta+e\}$
at 49,642 points. The selection functional was not evaluated numerically.

Run `python tools/verify_arbitrary_law_learned_oracle.py` with the pinned
toolchain. The audit restates every definition and theorem in full and fails
if a declaration of the two modules is not registered.
