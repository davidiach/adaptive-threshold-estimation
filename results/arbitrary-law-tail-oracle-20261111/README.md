# The oracle comparison of the tail certificate

This record covers statement (3) of the
[arbitrary-law tail certificate](../../docs/ARBITRARY_LAW_TAIL.md#comparison-with-the-rare-event-oracle):
past a finite onset, the [median certificate](../arbitrary-law-tail-median-20261111/README.md)
is at most a universal multiple of the rare-event oracle.

At depth $J$ write $t=2^{-J}$ and $N=4^J$. $K_{\mu,\rho}(B)$ is the
[entropy-tail selection functional](../../lean/ThresholdHC/EntropyTail/Model.lean)
of the rare-event theory, with its cap at $\rho$ and its infimum over all
submeasures. The **onset condition** at depth $J$ is
$$
 2048\,(J+1)\,2^{-J}/a^2\le\sqrt\rho ,
$$
where $a>0$ is the threshold of the lowest-gap quantile of mass $\rho$ of the
gap law. The statements hold for every probability law $\mu$ of positive gaps,
every measurable gap-dependent sign law and $0<\rho\le1/4$.

| Statement | Lean-checked guarantee |
|---|---|
| [Kernel on every gap](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailOracle.lean) | The unresolved probability of a coin of gap $d$ plus $w_J(d)/N$ is at most $2052\min\{1,t/d\}$. |
| [Kernel on the core](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailOracle.lean) | On gaps $d\ge a$ it is at most $(1024(J+1)+16)\,t^2/a^2$. |
| [Onset](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailOracle.lean) | There is a depth $J_0$, depending on $\mu$ and $\rho$ only, such that every depth $J\ge J_0$ meets the onset condition. |
| [Comparison](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailOracle.lean) | Under the onset condition, $u_J+W_J/N\le4096\,K_{\mu,\rho}(N)$, and the bound $\min\{1,128\max(u_J,W_J/N)\}$ of statement (1) is at most $524288\,K_{\mu,\rho}(N)$. |
| [Statement (3)](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailOracleLaw.lean) | For $m\ge8\log(2/\delta)$ probes with flip budget $4^J$ each, at a depth that meets the onset condition, with probability at least $1-\delta$, $F(t)\le U\le524288\,K_{\mu,\rho}(4^J)$. |
| [Every depth](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailOracleLaw.lean) | With $m_J\ge8\log(2J(J+1)/\delta)$ probes at depth $J$, with probability at least $1-\delta$: $F(2^{-J})\le U_J$ at every depth $J\ge1$, and $U_J\le524288\,K_{\mu,\rho}(4^J)$ at every depth that meets the onset condition, in particular at every $J\ge J_0$. |
| [One coin array](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailOracleLaw.lean) | The one-depth and every-depth statements hold on the coin array of the original simulation law, where probe $j$ of depth $J$ reads the coins `Nat.pair J (Nat.pair j i)`. |

The proof splits the gap law at its lowest-gap quantile of mass $\rho$, with a
fraction of a boundary atom when needed; this is the project's existing
[quantile split](../../lean/ThresholdHC/EntropyTailQuantile/QuantileSplit.lean).
The existing [quantile-tail floor](../../lean/ThresholdHC/EntropyTailQuantile/QuantileTailBound.lean)
bounds the quantile part by $2052K$. The core has gaps at least $a$, so under
the onset condition its part is at most $t\sqrt\rho$, and the existing
[objective floor](../../lean/ThresholdHC/EntropyTail/Objective.lean) gives
$K\ge2t\sqrt\rho$. The procedure receives neither $\rho$ nor the onset. No
inverse moment or tail regularity of the law is assumed, and atoms are
allowed.

The onset is large. For a point mass at $1/2$ and $\rho=1/4$ the condition
first holds at depth 19, which is $4^{19}$ flips for each probe. The constant
$524288$ is a rate constant and is not a practical guarantee.

With this record, statements (1) to (4) of the tail certificate are checked
for probes that read the coin array of the original experiment. It does not
include:

- Readers in the observable stage. The probes are defined on streams of tapes.
- The pilot of (A6) to (A8) in the
  [adaptation proof](../../docs/ARBITRARY_LAW_ADAPTATION.md), and the learned
  law's comparison with the oracle.
- The arbitrary-law adaptation theorem, which remains a paper proof.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/3e73b61de1cc5700e43fff4d1e489f9f267fb068),
the two new modules were built from source on Linux with Lean `v4.36.0-rc1`,
on top of a build of every project module made in the same environment and
against the Mathlib cache for the pinned revision. They compiled without
warnings. [26 exact statements](arbitrary_law_tail_oracle.lean) passed with
[26 transitive axiom reports](arbitrary_law_tail_oracle.log), one for each
declaration of the two modules, using only `propext`, `Classical.choice` and
`Quot.sound`. The whole-project audit
`python tools/verify_project_axioms.py --no-build` passed on the same build:
1,163 modules, 11,983 constants and 9,673 theorems, with no declared axiom. Its
kernel replay was not run locally. The [native record](status.json) lists the
source hash of every project module in the import closure of the new
modules.

One check outside Lean was run during review and is supporting evidence only.
With the envelope formulas as stated in Lean, both kernel bounds held at
200,000 random depths and gaps, and the split inequality
$u_J+W_J/N\le2052\,\tau_\nu(t)+t\sqrt\rho$ held in 78,190 cases over random
discrete laws that meet the onset condition. The selection functional itself
was not evaluated numerically.

Run `python tools/verify_arbitrary_law_tail_oracle.py` with the pinned
toolchain. The audit restates every definition and theorem in full and fails
if a declaration of the two modules is not registered.
