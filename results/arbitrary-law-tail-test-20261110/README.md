# The sign-neutral single-coin tail test

This record covers the single-coin primitive of the
[arbitrary-law tail certificate](../../docs/ARBITRARY_LAW_TAIL.md#a-sign-neutral-test-with-a-gap-dependent-cost).
One persistent coin is inspected after $n_k=4^k$ flips, $k=0,\ldots,J$. Check
$k$ resolves the coin when $|\bar X_{n_k}-1/2|>h_k/n_k$, with the integer
threshold $h_k=\lceil\sqrt{2n_k(J-k+2)}\rceil$. A tie continues. The coin is
unresolved when the terminal check also fails. Write $T$ for the flips bought,
$t=2^{-J}$ and $N=4^J$.

The coin model is the project's own: a coin of gap $d$ and positive sign has
iid flips with heads probability $1/2+d$, and one fresh coin of the original
population has the [actual population tape law](../../lean/ThresholdHC/ObservableSimulation/OriginalExperiment.lean)
for a gap law $\mu$ on $(0,1/2]$ and a measurable gap-dependent sign law $q$.

| Statement | Lean-checked guarantee |
|---|---|
| [Test and work cap](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailTest.lean) | $h_k$ is the least natural number with $h_k^2\ge 2n_k(J-k+2)$, and $h_J=2^{J+1}$. On every tape $1\le T\le N$. |
| [Observed prefix](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailTest.lean) | Two tapes that agree on the first $T$ flips have the same stopping check, the same work and the same unresolved indicator. |
| [Flip symmetry](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailTest.lean) | Complementing every flip preserves each check, the stopping check, the work and the unresolved indicator. |
| [Sign neutrality](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailTestLaw.lean) | Complementing flips maps the law of a coin with heads probability $p$ to that of $1-p$. For a bounded measurable statistic $G$ of one tape that is invariant under complementing, the mean of $G$ under the population tape law equals $\int \mathbb E_{1/2+d}[G]\,\mu(dd)$ for every probability law $\mu$ and every sign law $q$. |
| [Small gaps](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailTestProbability.lean) | If $d\le t$, the coin is unresolved with probability at least $1/2$. |
| [Large gaps](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailTestProbability.lean) | If $d\ge4t$, the coin is unresolved with probability at most $e^{-Nd^2/2}$. |
| [Unresolved mass](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailTestLaw.lean) | The unresolved probability $u_J$ of a fresh coin is the same for every sign law, and $\tfrac12\mu((0,t])\le u_J\le\int\min\{1,16(t/d)^2\}\,\mu(dd)$. |
| [Multiplier comparison](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailTestLaw.lean) | $u_J\le(\mu\otimes\mathcal L(V))\{(d,v):dv\le t\}$ for the [constructed multiplier](../arbitrary-law-light-20261106/README.md) $V$ of (A3). |
| [Work](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailTestProbability.lean) | For either sign, $\mathbb E_dT\le w_J(d)=\min\{N,\,1024d^{-2}(1+\log_2^+(d/t))\}$. For a fresh coin of the population, $\mathbb ET\le\int w_J\,d\mu$. |

The lower bound for small gaps is a union bound over the $J+1$ checks, each
bounded by a two-sided Hoeffding inequality. The upper bound for large gaps
uses the terminal check only. The work bound sums the increments $3\cdot4^k$
against the probability of passing check $k$, which decays geometrically from
the first check with $n_kd^2\ge36(J-k+2)$. The checks of one coin share its
flips; no statement treats them as independent samples. The population
statements hold for arbitrary probability laws of positive gaps, including
atoms, and assume no inverse moment.

This is statements (2), (2a) and (4) of the tail-certificate proof, and the
sign-neutrality claim before them. It is the single-coin primitive only:

- Inverse sampling over fresh coins, the median over probes, statement (1) and
  the oracle comparison (3) are not formalized.
- The test is defined on a tape of flips, with the observed-prefix statement
  above. It is not yet embedded as a reader in the observable stage, and no
  pause or resume semantics is stated.
- The [arbitrary-law adaptation theorem](../../docs/ARBITRARY_LAW_ADAPTATION.md)
  remains a paper proof.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/1204b139d4cf3431e0c81b9e943bc3b5a7415264),
the three new modules were built from source on Linux with Lean
`v4.36.0-rc1`, on top of a full build of every project module made in the
same environment and against the Mathlib cache for the pinned revision. They
compiled without warnings. [91 exact statements](arbitrary_law_tail_test.lean)
passed with [91 transitive axiom reports](arbitrary_law_tail_test.log), one
for each declaration of the three modules, using only `propext`,
`Classical.choice` and `Quot.sound`. The whole-project audit
`python tools/verify_project_axioms.py --no-build` passed on the same build:
1,155 modules, 11,799 constants and 9,507 theorems, with no declared axiom. Its
kernel replay was not run locally. The [native record](status.json) lists the
source hashes.

Run `python tools/verify_arbitrary_law_tail_test.py` with the pinned
toolchain. The audit restates every definition and theorem in full and fails
if a declaration of the three modules is not registered.
