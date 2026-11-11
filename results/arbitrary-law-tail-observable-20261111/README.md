# The tail certificate in the observable experiment

This record covers the observable embedding of the
[arbitrary-law tail certificate](../../docs/ARBITRARY_LAW_TAIL.md#inverse-sampling-under-a-physical-budget).
The earlier records prove the certificate for probes defined on the coin array
of the original experiment. Here the probes are run by a **reader**: a rule
that chooses the next coin to flip from the flips observed so far. The
estimator sees only flips, and its certificate is a function of the observed
word.

Write $F(x)=\mu((0,x])$, $u_J$ for the unresolved probability of one coin
at depth $J$, $W_J=\int w_J\,d\mu$, and $K_{\mu,\rho}(B)$ for the
[entropy-tail selection functional](../../lean/ThresholdHC/EntropyTail/Model.lean).
The probability statements hold for every probability law $\mu$ of positive
gaps and every measurable gap-dependent sign law, under the law of the
original hidden-gap experiment.

| Statement | Lean-checked guarantee |
|---|---|
| [Probe reader](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailProbeReader.lean) | A state machine tests coin 0, then coin 1, and so on with the [sign-neutral tail test](../arbitrary-law-tail-test-20261110/README.md), and keeps the probe's completed count. After $t$ flips of any table of coin tapes, the count computed from the observed word equals the completed count of the [capped probe](../arbitrary-law-tail-probe-20261110/README.md) at flip budget $t$. |
| [Schedule](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailProbeReader.lean) | After $t$ flips the reader is on the first coin whose test is not complete within $t$ flips. It buys the flips of each coin consecutively and never returns to a coin. |
| [Pause and resume](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailProbeReader.lean) | The observed word at a smaller budget is a prefix of the word at a larger one, and the count computed from the first $t$ flips of a longer block is the completed count at budget $t$. |
| [Blocks](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailBlockReader.lean) | When blocks run one after another and block $n$ reads the coins `Nat.pair n i`, the part of the observed word that block $n$ bought is the word its reader would observe alone on those coins. Coins of blocks that have not run are untouched. |
| [Median from the word](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailBlockReader.lean) | For $m$ probes with $b$ flips each, the median computed from the observed word equals the [median certificate](../arbitrary-law-tail-median-20261111/README.md) of probes reading the coins `Nat.pair j i`. Cut after $t$ flips, it equals that median with probe $j$ at flip budget $\min\{(t-jb)_+,b\}$. With one more level of blocks, depth $J$ reads the coins `Nat.pair J (Nat.pair j i)`. |
| [Estimator](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailObservable.lean) | The estimator buys its block of $n$ flips and reports a function of the observed word. It buys at most $n$ flips on every admissible path. |
| [Transfer](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailObservable.lean) | Every event about the observed word has the same probability under the law of the original experiment as the same event about the reader's word on the coin array of the original simulation law. |
| [Statement (1)](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailObservable.lean) | For $m\ge8\log(2/\delta)$ probes with $4^J$ flips each, the estimator buys at most $m4^J$ flips, and with probability at least $1-\delta$ its output $U$ satisfies $U\le\min\{1,128\max(u_J,W_J/4^J)\}$ and the certificate computed from the first $t$ observed flips is at least $F(2^{-J})$ for every $t$ at once. |
| [With a coin cap](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailObservable.lean) | With $b\ge1$ flips and coin cap $M\ge1$ for each probe, the upper bound is $\min\{1,128\max(u_J,W_J/b,1/M)\}$. |
| [Statement (3)](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailObservable.lean) | At a depth that meets the [onset condition](../arbitrary-law-tail-oracle-20261111/README.md), the output is at most $524288\,K_{\mu,\rho}(4^J)$, for $0<\rho\le1/4$. There is a finite onset $J_0$, depending on $\mu$ and $\rho$ only, past which every depth meets the condition. |
| [Depths up to $L$](../../lean/ThresholdHC/ArbitraryLawAdaptation/TailObservable.lean) | One estimator runs the depths $J\le L$ one after another, with $m_J\ge8\log(2J(J+1)/\delta)$ probes at depth $J$. With probability at least $1-\delta$, at every depth $1\le J\le L$ the certificate covers $F(2^{-J})$ at every pause and is at most $\min\{1,128\max(u_J,W_J/b_J,1/M_J)\}$; with $b_J=M_J=4^J$ it is at most $524288\,K_{\mu,\rho}(4^J)$ at every such depth that meets the onset condition. |

The coverage at every pause uses the earlier fact that the median covers
$F(2^{-J})$ for every choice of the probes' flip budgets. A cut after $t$
flips leaves complete probes, at most one interrupted probe and probes that
have not started, and a probe that has not started reports the trivial
certificate 1.

The reader buys every block in full. Flips bought after a probe has stopped
are charged and ignored, so the estimator's charge is its cap, $mb$ flips at
one depth, and not the smaller number of flips the probes use. The estimator
of the depths runs depth 0 as well, with $m_0$ probes of $b_0$ flips; the
probability statements are about the depths $1\le J\le L$.

This is the embedding of the certificate. It does not include:

- The pilot of (A6) to (A8) in the
  [adaptation proof](../../docs/ARBITRARY_LAW_ADAPTATION.md) as an instance of
  the [paid learning stage](../../lean/ThresholdHC/ArbitraryLawAdaptation/LearnedStage.lean),
  with its common number of probes, and the learned law's comparison with the
  oracle.
- An estimator that stops buying flips when its probes stop.
- The arbitrary-law adaptation theorem, which remains a paper proof.
- Python execution of the toolkit.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/fe95401a82e27d8c41d95f392a092ac8af4ef353),
the three new modules were built from source on Linux with Lean
`v4.36.0-rc1`, on top of a build of every project module made in the same
environment and against the Mathlib cache for the pinned revision. They
compiled without warnings. [68 exact statements](arbitrary_law_tail_observable.lean)
passed with [68 transitive axiom reports](arbitrary_law_tail_observable.log),
one for each declaration of the three modules, using only `propext`,
`Classical.choice` and `Quot.sound`; three of the declarations use no axiom.
The two structures are restated through their fields. The whole-project audit
`python tools/verify_project_axioms.py --no-build` passed on the same build:
1,166 modules, 12,130 constants and 9,775 theorems, with no declared axiom. Its
kernel replay was not run locally. The [native record](status.json) lists the
source hash of every project module in the import closure of the new
modules. Its base checkpoint is the head of the oracle-comparison change.

One check outside Lean was run during review and is supporting evidence only.
A literal transcription of the reader, the block reader and the word-level
certificates was run on random coin tapes. The count from the observed word
equalled a transcription of the tape-level count at 14,228 pairs of a run and
a budget. The median from the observed word equalled the tape-level median on
250 runs and the median of the
[toolkit's](../../toolkit/threshold_toolkit/tail_mass.py) probes, fed the same
coins, at 288 pauses. Every depth's certificate equalled the toolkit's on 60
runs of the reader of the depths.

Run `python tools/verify_arbitrary_law_tail_observable.py` with the pinned
toolchain. The audit restates every definition and theorem in full and fails
if a declaration of the three modules is not registered.
