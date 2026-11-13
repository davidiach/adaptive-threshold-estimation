# The race is monotone in the flips, and its error transfers

This record covers the first part of the
[robust use of the known-law estimator](../../docs/ARBITRARY_LAW_ADAPTATION.md#4-robust-use-of-the-known-law-estimator):
the raced classifier is monotone in the flips of its coin, so its error on a
coin of either sign does not increase when the gap grows, and its population
error under a law with larger gaps than its reference is bounded by the error
at the reference.

A tape of flips is below another when it has tails wherever the other has
tails. The race runs a negative test and a positive test on the even flips
against the [ordinary classifier](../../lean/ThresholdHC/BlindUpper/ClassifierProcedure.lean)
on the odd flips; the negative test has priority, and a terminal tie of the
ordinary classifier is negative. A test is **downward** when turning tails
into heads cannot make it fire, and **upward** when that cannot stop it from
firing.

| Statement | Lean-checked guarantee |
|---|---|
| [Coins](../../lean/ThresholdHC/RobustContinuation/TapeOrder.lean) | Flips built from common uniforms are monotone in the success probability. An upper set of tapes is at least as likely under the coin with the larger success probability, and a lower set at most as likely. |
| [Ordinary classifier](../../lean/ThresholdHC/RobustContinuation/ClassifierOrder.lean) | For every boundary sequence: when every running mean is raised, a positive decision stays positive and is not delayed, and a strictly earlier stop is a positive decision. The decision is monotone in the flips. |
| [Race](../../lean/ThresholdHC/RobustContinuation/RaceOrder.lean) | For a downward negative test and an upward positive test, the output of the race is monotone in the flips. |
| [Banks](../../lean/ThresholdHC/RobustContinuation/RaceOrder.lean) | The negative bank with allowance $\varepsilon\ge0$ is downward. The positive bank is upward for every reference law, every weight sequence and every allowance: the null probability of a word of flips does not increase, and its probability under the positive references does not decrease, when tails are turned into heads. |
| [One coin](../../lean/ThresholdHC/RobustContinuation/RaceOrder.lean) | For such tests and gaps $d\le d'$: the error of the race on a coin of gap $d'$ is at most its error on a coin of gap $d$, for a positive coin and for a negative coin. |
| [Transfer](../../lean/ThresholdHC/RobustContinuation/RobustLevelError.lean) | Let $\pi$ be a finite measure on pairs of gaps with $z_1\le z_2$ almost everywhere, and let the true law be the second marginal of $\pi$ plus a finite part $\mu_0$. For every sign law $q$ of the true gaps, the population error of the race is at most $\int[q(z_2)\,e_+(z_1)+(1-q(z_2))\,e_-(z_1)]\,d\pi+\mu_0(\text{all gaps})$, where $e_\pm$ are its errors on one coin. |
| [Bank from a reference law](../../lean/ThresholdHC/RobustContinuation/RobustLevelError.lean) | If moreover the first marginal of $\pi$ is $c\,\eta$ for a probability law $\eta$ of positive gaps and $c\ge0$, the race is the bank designed from $\eta$ with allowances $\varepsilon,u\ge0$, and $q$ has positive fraction at most $\rho$ under the true law: the population error at cap $2^L$ is at most $\rho\varepsilon+c\,u+c\int\min\{1,(2^Ld^2)^{-2}\}\,d\eta+\mu_0(\text{all gaps})$. |

With $c=1$ and $\mu_0=0$ the last row is the error bound of the
[known-law theorem](../../lean/ThresholdHC/EntropyTailUpper/PopulationErrors.lean)
with the reference law in place of the true law. The integral in the transfer
row is the error under the sign allocation that the coupling induces on the
reference gaps, written without a conditional expectation.

**Mass at zero.** A reference law $z_0\delta_0+(1-z_0)\eta$ is handled with
$c=1-z_0$, and $\mu_0$ the part of the true law coupled to the atom, of mass
$z_0$. That mass is charged in full. No coin of gap zero is used, and the
positive bank's null law is that of $\eta$: the atom's fair-coin likelihood
is not needed for this bound.

It does not include:

- **The coupling itself** as a construction from $\alpha\preceq\mu$, and the
  induced sign allocation as a sign law of the reference gaps. The
  statements take the coupling as given;
  [an increasing coupling exists](../../lean/ThresholdHC/ArbitraryLawAdaptation/CDFCoupling.lean)
  on the real line under CDF domination.
- **Work.** Increasing a gap can remove a wrong early exit, so the stopping
  time is not monotone; the work transfer (A15) is a separate argument.
- The corrections, the plan run under the true law, the physical-cap median
  and the connection to the paid stage.
- The robust continuation as a whole, the all-budget controller and the
  arbitrary-law adaptation theorem, which remains a paper proof.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/c7e30e5281125f6c9e9fb12af096b6cbdd81b57f),
the four new modules were built from source on Linux with Lean `v4.36.0-rc1`,
on top of a build of every project module made in the same environment and
against the Mathlib cache for the pinned revision. They compiled without
warnings. [33 exact statements](robust_error_transfer.lean) passed with
[33 transitive axiom reports](robust_error_transfer.log), one for each
declaration of the four modules. Four declarations use no axiom; the others
use only `propext`, `Classical.choice` and `Quot.sound`. The whole-project
audit `python tools/verify_project_axioms.py --no-build` passed on the same
build: 1,187 modules, 12,589 constants and 10,164 theorems, with no declared
axiom. Its kernel replay was not run locally. The
[native record](status.json) lists the source hash of every project module
in the import closure of the new modules. Its base checkpoint is `main` after
the planner change.

Run `python tools/verify_robust_error_transfer.py` with the pinned toolchain.
The audit restates every definition and theorem in full and fails if a
declaration of the four modules is not registered.
