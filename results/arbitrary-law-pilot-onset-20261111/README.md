# The pilot's work estimates and onset

This record covers the first part of the learned law's oracle comparison in
the [arbitrary-law adaptation proof](../../docs/ARBITRARY_LAW_ADAPTATION.md#3-the-learned-law-retains-the-oracle-rate):
the lowest-gap split of the gap law, the work estimates (A12), the onset, and
the two floors of the selection functional that (A14) uses.

Fix $0<\rho\le1$ and a probability law $\mu$ of positive gaps. Split $\mu$ at
its lowest-gap quantile of mass $\rho$: $\mu=\nu+\sigma$, where $\nu$ has mass
$\rho$ and a boundary atom is divided between the two parts. $a$ is the
quantile threshold. For the [pilot](../arbitrary-law-pilot-20261111/README.md)
of target depth $J$ write $N=4^J$, $t=2^{-J}$, $b_j$ for the flip budget of
depth $j$ and $M$ for the coin cap. $W_{j,\xi}=\int w_j\,d\xi$ integrates the
work envelope of depth $j$, $\tau_\nu(s)=\int\min\{1,s/d\}\,d\nu$ is the tail
modulus, and $K=K_{\mu,\rho}(N)$ is the
[entropy-tail selection functional](../../lean/ThresholdHC/EntropyTail/Model.lean).
All statements are in
[PilotOnset.lean](../../lean/ThresholdHC/ArbitraryLawAdaptation/PilotOnset.lean).

| Statement | Lean-checked guarantee |
|---|---|
| Split | $\nu+\sigma=\mu$, $\nu$ has mass $\rho$ and gaps at most $a$, $\sigma$ has gaps at least $a$, and $a>0$. |
| Kernel bounds | $w_j(d)\le2048\cdot4^j\min\{1,2^{-j}/d\}$ on every gap, and $w_j(d)\le1024(j+1)/a^2$ on gaps $d\ge a$. For $0<t\le s$, $\tau_\nu(s)\le(s/t)\,\tau_\nu(t)$. |
| (A12), quantile part | $W_{j,\nu}/b_j\le8192\,\tau_\nu(t)$ at every depth $1\le j\le J$. |
| (A12), core part | $W_{j,\sigma}/b_j\le2048\,(J+1)^3t^2/a^2$ at every depth $1\le j\le J$. |
| Onset | The pilot's onset condition at depth $J$ is $2048\,(J+1)^3\,2^{-J}/a^2\le\sqrt\rho$. There is a depth $J_0$, depending on $\mu$ and $\rho$ only, such that every $J\ge J_0$ meets it. It implies the [onset condition of the tail certificate](../arbitrary-law-tail-oracle-20261111/README.md) and $2t\le\sqrt\rho$. |
| Quantile-tail floor | $\tau_\nu(t)\le K$. |
| (A12) against the oracle | Under the onset condition, for $\rho\le1/4$: $W_j/b_j\le8193\,K$ at every depth $1\le j\le J$. |
| Elementary floor | Under the onset condition, for $\rho\le1/4$: $2t\sqrt\rho\le K$. |
| Coin cap | $1/M\le\sqrt\rho\,t/8$ for every $\rho>0$, and under the onset condition, for $\rho\le1/4$, $16/M\le K$. |

The quantile part of (A12) uses the geometric part $2^{J+j-2}$ of the budget
and the scaling of the tail modulus. The core part uses the reciprocal part
$N/(2j(j+1))$. The split is the project's existing
[quantile split](../../lean/ThresholdHC/EntropyTailQuantile/QuantileSplit.lean),
and the two floors come from the existing
[quantile-tail floor](../../lean/ThresholdHC/EntropyTailQuantile/QuantileTailBound.lean)
and [objective floor](../../lean/ThresholdHC/EntropyTail/Objective.lean). The
constant $8193$ rounds up the paper's $8192+1/2$. These are deterministic
statements about the gap law. The threshold $a$ and the onset are proof
quantities; the pilot receives neither.

The onset is large. For a point mass at $1/2$ and $\rho=1/4$ the condition
first holds at depth 29.

This is the first part of (A11). It does not include:

- The comparison of the unresolved probabilities with the multiplier law, the
  learned-CDF bound (A13), and the bound $e<2^{22}K$ of (A14).
- The clipped-CDF witness and the comparison
  $K_{\bar\mu,\rho}(N)\le2^{24}K_{\mu,\rho}(N)$ on the pilot event.
- The robust continuation, the all-budget controller and the arbitrary-law
  adaptation theorem, which remains a paper proof.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/67b03ade573a73df3c38ae966d4bc75247123453),
the new module was built from source on Linux with Lean `v4.36.0-rc1`, on top
of a build of every project module made in the same environment and against
the Mathlib cache for the pinned revision. It compiled without warnings.
[25 exact statements](arbitrary_law_pilot_onset.lean) passed with
[25 transitive axiom reports](arbitrary_law_pilot_onset.log), one for each
declaration of the module, using only `propext`, `Classical.choice` and
`Quot.sound`. The whole-project audit
`python tools/verify_project_axioms.py --no-build` passed on the same build:
1,169 modules, 12,274 constants and 9,902 theorems, with no declared axiom. Its
kernel replay was not run locally. The [native record](status.json) lists the
source hash of every project module in the import closure of the new module.

One check outside Lean was run during review and is supporting evidence only.
With the envelope and budget formulas as stated in Lean, both parts of (A12)
held in 206,507 cases over random discrete laws, depths and rarities; the
coin-cap bound held exactly in 120 cases; and the onset for a point mass at
$1/2$ with $\rho=1/4$ was depth 29. The selection functional itself was not
evaluated numerically.

Run `python tools/verify_arbitrary_law_pilot_onset.py` with the pinned
toolchain. The audit restates every definition and theorem in full and fails
if a declaration of the module is not registered.
