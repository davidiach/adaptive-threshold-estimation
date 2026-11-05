# RMS obstruction transfer and additive localization

For a known positive-gap law and $0<\rho\le1/4$, suppose every
capped bounded one-coin estimator with bias at most $b>0$ and
variance at most $V$ on the half-prior class satisfies
$V\mathbb E_0T\ge J>0$. The checked RMS lower bound is

\[
R_{\mu,\rho}(B)\ge
\frac1{128}\min\{b,\sqrt{J/B}\},\qquad B>0.
\]

For finite nonzero submeasures $\sigma_i$ with
$\sum_i\sigma_i\le\mu$, masses $\tau_i$ and normalized laws
$\nu_i$, suppose the component obstructions are $(b_i,J_i)$
at rarities $0<r_i\le1/4$, with $\sum_i\tau_i r_i\le\rho$.
Then

\[
R_{\mu,\rho}(B)\ge
\frac1{128}\sum_i\tau_i\min\{b_i,\sqrt{J_i/B}\}.
\]

Both conclusions cover each observable estimator with a uniform
expected budget and the minimax infimum. The submeasure supports
may overlap.

## Original experiment and constants

The [common-pair construction](COMMON_PAIRS.md) gives separation
$s=\min\{b,\sqrt{J/B}\}/32$ and the local Hellinger coefficient
$\kappa\le42/(1024B)$ against null work.

The finite adaptive population decomposition charges all local
losses to work under the same midpoint law. Null work is at most
twice midpoint work. Restriction to the finite labels used at a
finite horizon, followed by integration over the arbitrary private
seed, proves the original finite-prefix bound.

Finite work at both endpoints supplies stopped-prefix
reconstruction. The existing terminal-affinity theorem then gives,
for every finite terminal decision,

\[
1-\operatorname{Aff}\le2\kappa B\le21/256<1/10.
\]

For target means $a<b$, squared risks below $(b-a)^2/16$
would make each midpoint-testing error at most
$1/4$. Their binary affinity is at most $7/8$ by Cauchy–Schwarz,
contradicting affinity at least $9/10$. Thus the maximum RMS
risk is at least one quarter of the target separation.

The additive theorem uses the already checked global-prior,
observation-law and work construction for overlapping submeasures.
Each component uses $s_i=\min\{b_i,\sqrt{J_i/B}\}/32$.
All share the same local coefficient $42/(1024B)$, and their
target separations add with weights $\tau_i$.

## Proof map

| Step | Native proof |
|---|---|
| Arbitrary creation labels and actual finite-prefix work | [Creation](../lean/ThresholdHC/RMSLocalization/Creation.lean) |
| Arbitrary private seed and midpoint prior | [Observable](../lean/ThresholdHC/RMSLocalization/Observable.lean) |
| Original stopped finite-decision bound | [Terminal](../lean/ThresholdHC/RMSLocalization/Terminal.lean) |
| Binary affinity and squared/RMS risk constants | [BinaryAffinity](../lean/ThresholdHC/RMSLocalization/BinaryAffinity.lean), [Testing](../lean/ThresholdHC/RMSLocalization/Testing.lean) |
| Estimator-level pair lower bound | [PairRisk](../lean/ThresholdHC/RMSLocalization/PairRisk.lean) |
| Common-pair and obstruction conclusions | [CommonPair](../lean/ThresholdHC/RMSLocalization/CommonPair.lean) |
| Mixture and normalized-submeasure conclusions | [Additive](../lean/ThresholdHC/RMSLocalization/Additive.lean), [Full](../lean/ThresholdHC/RMSLocalization/Full.lean) |

The [native record](../results/rms-localization-20261105/README.md)
checks 15 exact statements and 15 transitive axiom reports.
The [manuscript proof](../paper/v6/rms-localization.tex) records the
hypotheses and constants. The sharp quantile-factor characterization
remains a paper proof, alongside the open research questions listed
in the [workplan](WORKPLAN.md#current-priorities).
