# The level certificates of the race under a law coupled above its reference

This record covers the error and the expected work of one level race of the
known-law estimator when the race is designed from a reference law and run
under a true law with larger gaps, as in the
[robust use of the known-law estimator](../../docs/ARBITRARY_LAW_ADAPTATION.md#4-robust-use-of-the-known-law-estimator).
It integrates the [per-coin work bounds](../robust-coin-work-20261113/README.md)
over a coupling and combines them with the
[error transfer](../robust-error-transfer-20261113/README.md).

**Reference.** The positive part of the reference law is $c\,\eta$, with
$c>0$ and $\eta$ a probability law of positive gaps; a reference law
$z_0\delta_0+(1-z_0)\eta$ has $c=1-z_0$. Its design is
$\sigma+\tau+\zeta=c\,\eta$: selected core, resolved tail and unresolved
part. $\Gamma$ is the cost entropy of the band costs of $\sigma$,
$A=\int d^{-2}\,d\sigma$, $H=\int d^{-1}\,d\tau$ and $O_\tau(M)$ the ordinary
work of $\tau$ at cap $M$.

**Bank.** Band weights of $\sigma$, null law $\eta$, negative allowance
$\varepsilon$ and positive allowance $\rho\varepsilon/c$. At level $l$,
$\varepsilon_l=\tfrac1{64}16^{-l}$ and $\delta_l=\rho\,16^{-(l+1)}$. With
$c=1$ this is the bank of the known-law theorem.

**True law.** A finite measure $\pi$ on pairs of gaps with first marginal
$c\,\eta$ and $z_1\le z_2$ almost everywhere; the true law is the second
marginal of $\pi$ plus a finite part $\mu_0$ coupled to no positive
reference gap. The sign law $q$ of the true gaps has positive fraction at
most $\rho$ under the true law. $W_q(d)$ is the expected work of the race on
a coin of gap $d$ with sign law $q$.

| Statement | Lean-checked guarantee |
|---|---|
| [Split of a coupling](../../lean/ThresholdHC/RobustContinuation/CouplingSplit.lean) | A measure whose image under a measurable map is a sum $\nu_1+\nu_2$ of finite measures is a sum $\pi_1+\pi_2$ with images $\nu_1$ and $\nu_2$; the same for three measures. |
| [Positive coin](../../lean/ThresholdHC/RobustContinuation/RobustLevelCertificates.lean) | For a reference gap $d_0$ in band $j$ with weight $0<w_j\le1$ and a positive coin of gap $d\ge d_0$: the expected work is at most $12\,A(d_0)/d_0^2$, where $A(d_0)$ is the positive allowance with the three-piece surcharge of the design at $d_0$ and rarity $\rho$. |
| [One coin with a sign law](../../lean/ThresholdHC/RobustContinuation/RobustLevelCertificates.lean) | $W_q(d)\le12d_0^{-2}\bigl(1+\log\tfrac1\varepsilon+\log\tfrac1{w_j}\bigr)+12\,q(d)\,d_0^{-2}\log_+\bigl((\zeta(\text{all gaps})+Ad_0^2+Hd_0)/\rho\bigr)$. |
| [Selected core](../../lean/ThresholdHC/RobustContinuation/RobustLevelCertificates.lean) | For a coupling with first marginal $\sigma$, $z_1\le z_2$ almost everywhere and $\int q(z_2)\,d\pi\le\rho$: $\int W_q(z_2)\,d\pi\le12\Gamma+12A\log\tfrac1\varepsilon+12(\log3+1)A+6H^2/\rho$, and at level $l$ at most $128(l+1)\Gamma+6H^2/\rho$. |
| [Resolved tail](../../lean/ThresholdHC/RobustContinuation/RobustLevelCertificates.lean) | For any race and a coupling with first marginal $\tau$ and $z_1\le z_2$ almost everywhere: $\int W_q(z_2)\,d\pi\le2\,O_\tau(M)$. |
| [Unresolved part](../../lean/ThresholdHC/RobustContinuation/RobustLevelCertificates.lean) | For any race and any finite $\pi$: $\int W_q(z_2)\,d\pi\le2M\,\pi(\text{all pairs})$. |
| [Level work](../../lean/ThresholdHC/RobustContinuation/RobustLevelCertificates.lean) | Under the true law, the expected work of the level race at cap $M=2^L$ is at most $128(l+1)\Gamma+6H^2/\rho+2\,O_\tau(M)+2M\bigl(\zeta(\text{all gaps})+\mu_0(\text{all gaps})\bigr)$, when $\zeta(\text{all gaps})\le\rho$. It is stated for one coupling with first marginal $c\,\eta$, and for three couplings with first marginals $\sigma$, $\tau$ and $\zeta$, of which the last need not be increasing. |
| [Level error](../../lean/ThresholdHC/RobustContinuation/RobustLevelCertificates.lean) | At a cap $4^k$ with resolved error $\eta_{\sigma+\tau}(4^k)\le\delta_l/8$, and with $\zeta(\text{all gaps})+\mu_0(\text{all gaps})\le\delta_l/8$: the error of the level race under the true law is at most $\delta_l$, for every weight sequence of total one. |

The work bound is the level-work certificate of the
[known-law theorem](../../lean/ThresholdHC/EntropyTailAssembly/LevelCertificates.lean)
with the integrals of the reference design and $\mu_0$ added to the
unresolved mass. It is the [level price](../known-law-planner-20261112/README.md)
of a plan whose unresolved mass is $z=\zeta(\text{all gaps})+\mu_0(\text{all gaps})$,
which for a reference law with mass $z_0$ at zero is the $z=z_0+\zeta(\text{all gaps})$
of the [zero-atom design](../known-law-plan-tight-rate-20261112/README.md).

The Lean proof differs from the paper argument in three ways.

- **No induced sign allocation.** The rarity surcharge at a reference gap is
  at most $\log3\,d_0^{-2}+A/\rho+H^2/(2\rho^2)$, as in the known-law
  proof. It is multiplied by the sign law at the true gap and integrated
  over the coupling, where $\int q(z_2)\,d\pi\le\rho$ because the second
  marginal is at most the true law. The conditional law of the sign given
  the reference gap is never formed.
- **No crossing times.** The per-coin bounds hold at the reference gap for
  every larger gap without a crossing time that ignores wrong exits.
- **Null law of the positive part.** The bank's null law is $\eta$, not the
  reference law with its mass at zero, and the positive allowance is
  $\rho\varepsilon/c$. Mass at zero in the reference is charged through
  $\mu_0$: at most its mass to the error and its mass times $2M$ to the
  work. No coin of gap zero and no fair-coin likelihood is used. The bank
  that evaluates the null mixture of the whole reference law, as the toolkit
  does, is a different test and is not the one checked.

It does not include:

- **The coupling in this form.** A coupling with first marginal $c\,\eta$ and
  the uncoupled part $\mu_0$ are hypotheses. Deriving them from CDF
  domination of the reference law by the true law is not part of this record.
- **The corrections and the plan under the true law**: the second moments of
  the differences of consecutive level races, the multilevel sum, and the
  work and error of the plan as an estimator.
- The physical-cap median and the connection to the paid stage.
- The robust continuation as a whole, the all-budget controller and the
  arbitrary-law adaptation theorem, which remains a paper proof.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/aee4f8db547de7a7984a2f659f7260710a8c0598),
the two new modules were built from source on Linux with Lean `v4.36.0-rc1`,
on top of a build of every project module made in the same environment and
against the Mathlib cache for the pinned revision. They compiled without
warnings. [18 exact statements](robust_level_certificates.lean) passed with
[18 transitive axiom reports](robust_level_certificates.log), one for each
declaration of the two modules, using only `propext`, `Classical.choice` and
`Quot.sound`. The whole-project audit
`python tools/verify_project_axioms.py --no-build` passed on the same build:
1,190 modules, 12,645 constants and 10,220 theorems, with no declared axiom.
Its kernel replay was not run locally. The [native record](status.json) lists
the source hash of every project module in the import closure of the new
modules. Its base checkpoint is the merge of the
[robust-work change](../robust-coin-work-20261113/README.md).

No numerical side check was run: the statements are integrals of bounds
inherited from checked theorems.

Run `python tools/verify_robust_level_certificates.py` with the pinned
toolchain. The audit restates every theorem in full and fails if a
declaration of the two modules is not registered.
