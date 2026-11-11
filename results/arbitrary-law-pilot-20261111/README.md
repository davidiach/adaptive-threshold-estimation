# The capped multi-depth pilot

This record covers the pilot of the
[arbitrary-law adaptation proof](../../docs/ARBITRARY_LAW_ADAPTATION.md#2-learning-the-envelope-under-one-physical-cap):
its budgets and caps (A6), the event (A8), the learned law (A9) and the cap
inequalities (A10).

Fix a target depth $J\ge1$ and write $N=4^J$. The pilot runs a common number
$m$ of [tail probes](../arbitrary-law-tail-probe-20261110/README.md) at every
depth $j=1,\dots,J$. Each probe of depth $j$ has the flip budget
$b_j=\lceil N/(2j(j+1))\rceil+2^{J+j-2}$, and every probe has the
completed-coin cap $M=\lceil\sqrt{64N/\rho}\rceil$. $U_j$ is the median of the
certificates of the $m$ probes of depth $j$. Write $F(x)=\mu((0,x])$, $u_j$
for the unresolved probability of one coin at depth $j$, and
$W_j=\int w_j\,d\mu$. The probability statements hold for every probability
law $\mu$ of positive gaps and every measurable gap-dependent sign law.

| Statement | Lean-checked guarantee |
|---|---|
| [Caps (A10)](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailPilot.lean) | $N/2\le\sum_{j=1}^Jb_j\le N$ for every $J\ge1$. The pilot buys $m\sum_jb_j\le mN$ flips. |
| [Depth one](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailPilot.lean) | No check of a depth-one test can resolve a coin. A depth-one probe counts at most one coin and its certificate is 1, for every word of flips. |
| [Reader](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailPilot.lean) | Block $i$ of the pilot's reader runs the $m$ probes of depth $i+1$, probe $k$ on the coins `Nat.pair i (Nat.pair k c)`. The certificate of each depth computed from the observed word equals the [median](../arbitrary-law-tail-median-20261111/README.md) of the probes on those coins, and lies in $(0,1]$. |
| [Event (A8)](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailPilotLaw.lean) | For $m\ge8\log(2J/\varepsilon)$, with probability at least $1-\varepsilon$, at every depth $1\le j\le J$ at once: $F(2^{-j})\le U_j\le128\,(u_j+W_j/b_j+1/M)$. The pilot fails with probability at most $2Je^{-m/8}$. |
| [Pilot alone](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailPilotLaw.lean) | An estimator that runs only the pilot buys at most $m\sum_jb_j$ flips on every admissible path, and (A8) holds for its certificates under the law of the original hidden-gap experiment. |
| [Pilot in the stage](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailPilotLaw.lean) | The pilot is installed in the [paid learning stage](../../lean/ThresholdHC/ArbitraryLawAdaptation/LearnedStage.lean). Its probes read the coins `Nat.pair 0 (Nat.pair i (Nat.pair k c))`, the continuation reads the fresh coins `Nat.pair 1 i`, and the stage buys at most $m\sum_jb_j$ flips plus the continuation's on every admissible path. (A8) holds for the certificates the stage reads off the pilot's word, on the coin array of the original simulation law. |
| [Learned law (A9)](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailPilotLaw.lean) | With $c_j=\min_{i\le j}U_i$, the stage's law is $c_J\delta_0+\sum_{j=1}^{J-1}(c_j-c_{j+1})\delta_{2^{-(j+1)}}$. It is a probability law on every observed word. Its mass at zero is $c_J$, and its distribution function at the grid point $2^{-(j+1)}$ is $c_j$. |
| [Domination](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailPilotLaw.lean) | When the certificates cover $F(2^{-j})$ at every depth, the learned law dominates $\mu$ in distribution at every point. So on the event (A8), which has probability at least $1-\varepsilon$, the stage's learned law dominates $\mu$. |

The union over depths is finite and uses the same number of probes at every
depth, unlike the [every-depth statement](../arbitrary-law-tail-median-20261111/README.md)
of the tail certificate. The proof needs no parity of $m$. The learned law is
computed from the certificates read off the observed word; no latent count of
small gaps enters it. The domination step is the existing
[finite CDF envelope](../arbitrary-law-envelope-20261106/README.md) applied to
those certificates.

As in the [observable tail certificate](../arbitrary-law-tail-observable-20261111/README.md),
the reader buys every block in full, so the pilot is charged its cap
$m\sum_jb_j$ on every path. The paper's remark that the coin cap lets
easy-law pilots stop early is not used and is not formalized.

This is the pilot and its learned law. It does not include:

- The learned law's comparison with the oracle past a finite onset, (A11) to
  (A14) of the adaptation proof.
- The robust continuation, and the event (A8) stated under the law of the
  experiment of the whole stage. It is stated there for the pilot run alone,
  and on the coin array for the stage.
- The all-budget controller and the arbitrary-law adaptation theorem, which
  remains a paper proof.
- Python execution of the toolkit.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/89be8c17651b94481ac138820aafb60b073c8008),
the two new modules were built from source on Linux with Lean `v4.36.0-rc1`,
on top of a build of every project module made in the same environment and
against the Mathlib cache for the pinned revision. They compiled without
warnings. [66 exact statements](arbitrary_law_pilot.lean) passed with
[66 transitive axiom reports](arbitrary_law_pilot.log), one for each
declaration of the two modules, using only `propext`, `Classical.choice` and
`Quot.sound`; two of the declarations use no axiom. The stage is restated
through its data fields. The whole-project audit
`python tools/verify_project_axioms.py --no-build` passed on the same build:
1,168 modules, 12,232 constants and 9,861 theorems, with no declared axiom. Its
kernel replay was not run locally. The [native record](status.json) lists the
source hash of every project module in the import closure of the new
modules. Its base checkpoint is the head of the observable tail-certificate
change.

One check outside Lean was run during review and is supporting evidence only.
A literal transcription of the budgets, the coin cap and the flip cap agreed
with the [toolkit's envelope planner](../../toolkit/threshold_toolkit/gap_envelope.py)
on 96 plans, the toolkit's number of probes met $m\ge8\log(2J/\varepsilon)$ on
each, and $N/2\le\sum_jb_j\le N$ held for $J=1,\dots,40$. A transcription of
the reader and the certificates was run against the toolkit's pilot program on
the same coins: the prefix minima and the mass at zero were equal on 40 runs,
and depth one returned 1 on each.

Run `python tools/verify_arbitrary_law_pilot.py` with the pinned toolchain.
The audit restates every definition and theorem in full and fails if a
declaration of the two modules is not registered.
