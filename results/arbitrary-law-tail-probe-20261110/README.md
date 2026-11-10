# The capped tail probe

This record covers one probe of the
[inverse-sampling step](../../docs/ARBITRARY_LAW_TAIL.md#inverse-sampling-under-a-physical-budget)
of the arbitrary-law tail certificate, with the coin cap of
[adaptation (A7)](../../docs/ARBITRARY_LAW_ADAPTATION.md#2-learning-the-envelope-under-one-physical-cap).
Fresh coins are tested one after another with the
[sign-neutral tail test](../arbitrary-law-tail-test-20261110/README.md) at
depth $J$. The probe stops when it completes an unresolved coin, when it has
completed $M$ coins, or when its flip budget $b$ is exhausted. After $n$
completed coins it returns $V=\min\{1,8/n\}$, and $V=1$ when $n=0$.

The stream of fresh coins is the project's own: the coin array of the
[original simulation law](../../lean/ThresholdHC/ObservableSimulation/OriginalExperiment.lean),
which is a sequence of independent tapes with the actual population tape law
for a gap law $\mu$ on $(0,1/2]$ and a measurable gap-dependent sign law $q$.
Write $t=2^{-J}$, $F(t)=\mu((0,t])$, $u_J$ for the unresolved probability of
one coin, and $W_J=\int w_J\,d\mu$ for the integral of the bounded work
envelope.

| Statement | Lean-checked guarantee |
|---|---|
| [Probe and caps](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailProbe.lean) | On every stream at most $\min\{b,M\}$ coins are completed, and the charge is at most $b$ and at most $M4^J$. Every flip of every completed coin is charged. |
| [Interrupted coin](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailProbe.lean) | A probe that has stopped is charged exactly its completed coins. A probe that the budget interrupts is charged the whole budget, and its next coin is not counted as completed. |
| [Budget monotonicity](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailProbe.lean) | Raising the flip budget or the coin cap never lowers the completed count, and raising the budget never lowers the charge. A coin cap of at least $b$ does not change the completed count. |
| [Bought flips](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailProbe.lean) | Two streams that agree on the bought flips have the same completed count, the same charge and the same final verdict. |
| [Coin array](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailProbeLaw.lean) | For every adaptive estimator, the coin array of the original simulation law is the stream of independent fresh coins. |
| [Coverage](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailProbeLaw.lean) | With probability at least $7/8$, $F(t)\le V$ at every flip budget and every coin cap simultaneously, for every probability law $\mu$ and every sign law $q$. |
| [Performance with the coin cap](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailProbeLaw.lean) | For every $b\ge1$ and $M\ge1$, with probability at least $3/4$, $V\le\min\{1,128\max(u_J,W_J/b,1/M)\}$. This is (A7). |
| [Performance without a coin cap](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailProbeLaw.lean) | For every $b\ge1$ and $M\ge b$, with probability at least $3/4$, $V\le\min\{1,128\max(u_J,W_J/b)\}$. This is (5) of the tail certificate. |

The [general statements](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailProbeProbability.lean)
hold for independent coins whose tapes share any probability law. Coverage
needs only $F\le1$ and $F\le2u$, where $u$ is the unresolved probability of
one coin. Its proof bounds the event that the first $\lfloor4/u\rfloor$ coins
are all resolved, which has probability $(1-u)^{\lfloor4/u\rfloor}\le e^{-3}$.
It does not treat the number of completed coins as a fixed sample size, so it
covers budgets chosen from the observed path. Performance joins two events by
a union bound: an unresolved coin among the first $q=\lfloor1/(8A)\rfloor$
coins, and their combined work exceeding $b$, which Markov's inequality bounds.
The two events are not assumed independent. The population statements follow
from $F(t)/2\le u_J$ and $\mathbb ET\le W_J$ of the tail-test record, and
assume no inverse moment.

This is the single-probe part of the inverse-sampling step. It does not
include:

- The median over independent probes and statement (1) of the tail
  certificate.
- The oracle comparison (3), its lowest-gap quantile decomposition and its
  onset.
- The simultaneous statement across depths, and the multi-depth pilot (A8).
- A reader in the observable stage. The probe is defined on a stream of tapes,
  with the bought-flips statement above. No pause or resume semantics is
  stated beyond monotonicity in the budget.
- The [arbitrary-law adaptation theorem](../../docs/ARBITRARY_LAW_ADAPTATION.md),
  which remains a paper proof.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/fede04aef33910b0dd6d4f3185406c88cff8de3e),
the three new modules were built from source on Linux with Lean
`v4.36.0-rc1`, on top of a build of every project module made in the same
environment and against the Mathlib cache for the pinned revision. They
compiled without warnings. [69 exact statements](arbitrary_law_tail_probe.lean)
passed with [69 transitive axiom reports](arbitrary_law_tail_probe.log), one
for each declaration of the three modules, using only `propext`,
`Classical.choice` and `Quot.sound`. The whole-project audit
`python tools/verify_project_axioms.py --no-build` passed on the same build:
1,158 modules, 11,885 constants and 9,585 theorems, with no declared axiom. Its
kernel replay was not run locally. The [native record](status.json) lists the
source hash of every project module in the import closure of the new
modules.

Two checks outside Lean were run during review and are supporting evidence
only. A literal transcription of the probe's definitions agreed with an
independent flip-by-flip simulation on 6,000 random streams, and with the
[toolkit probe](../../toolkit/threshold_toolkit/tail_mass.py) on the 2,230 of
them that have no active coin cap. A Monte Carlo run over five gap laws at
depths two to four found no violation of either probability bound; the
performance bound was far from binding at the budgets tried.

Run `python tools/verify_arbitrary_law_tail_probe.py` with the pinned
toolchain. The audit restates every definition and theorem in full and fails
if a declaration of the three modules is not registered.
