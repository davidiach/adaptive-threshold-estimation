# Fractional-submeasure confidence localization

Let $\sigma_i$ be finitely many nonzero submeasures with
$\sum_i\sigma_i\le\mu$. Write $\tau_i=\sigma_i((0,1/2])$ and
$\nu_i=\sigma_i/\tau_i$. The supports may overlap.

Suppose each normalized component has a variance–null-work obstruction
$(b_i,J_i)$ on its half-prior class with rarity $0<r_i\le1/4$, and
$\sum_i\tau_i r_i\le\rho$. For $B>0$ and $0<\delta\le1/4$, the
checked lower bound is

\[
r_{\rm exp}(B,\delta)\ge
\frac1{128}\sum_i\tau_i
\min\{b_i,\sqrt{J_i\log(1/\delta)/B}\}.
\]

The bound applies to actual observable estimators satisfying a uniform
expected budget on the global rarity class, and to the minimax infimum
over arbitrary measurable private seed spaces.

## Hypotheses

Each obstruction quantifies over actual capped bounded single-coin
estimators on $\nu_i$. Uniform bias at most $b_i$ and variance at most
$V$ must imply $V\mathbb E_{0,i}T\ge J_i>0$.
The [common-pair theorem](COMMON_PAIRS.md) constructs the
policy-uniform pairs internally from these premises. The application
to a particular law still needs proofs of its component obstructions.

## Original observation law

The proof combines the positive-sign measures
$\sum_i\tau_i q_i\nu_i$. Their doubled mass is dominated by $\mu$,
so their Radon–Nikodym densities give measurable global priors
bounded by one half. Clipping at one half preserves the measure
identity and makes the bound hold at every gap.

The negative-sign measure contains the common all-negative residual
$\mu-\sum_i\sigma_i$. Pushing both sign measures through the actual
Bernoulli-parameter, tape and stopped-statistic maps gives exact
mixture laws. The finite affinity inequality then bounds the global
Hellinger loss by the weighted component losses.

The all-negative expected work decomposes with the same weights
and a nonnegative residual cost. This proves that the original
algorithm pays for all component contributions. The existing stopped
$16/3$ KL bound and confidence test finish the proof.

## Proof map

| Step | Native proof |
|---|---|
| Normalized submeasures and residual | [Submeasures](../lean/ThresholdHC/AdditiveConfidence/Submeasures.lean), [Decomposition](../lean/ThresholdHC/AdditiveConfidence/Decomposition.lean) |
| Measurable half-prior density and exact targets | [HalfDensity](../lean/ThresholdHC/AdditiveConfidence/HalfDensity.lean), [PositiveMass](../lean/ThresholdHC/AdditiveConfidence/PositiveMass.lean), [NegativeMass](../lean/ThresholdHC/AdditiveConfidence/NegativeMass.lean) |
| Exact parameter, tape and statistic mixtures | [ParameterMixture](../lean/ThresholdHC/AdditiveConfidence/ParameterMixture.lean), [InputMixture](../lean/ThresholdHC/AdditiveConfidence/InputMixture.lean), [StatisticMixture](../lean/ThresholdHC/AdditiveConfidence/StatisticMixture.lean), [StatisticMass](../lean/ThresholdHC/AdditiveConfidence/StatisticMass.lean) |
| Affinity and original work | [FiniteMixture](../lean/ThresholdHC/AdditiveConfidence/FiniteMixture.lean), [WorkMixture](../lean/ThresholdHC/AdditiveConfidence/WorkMixture.lean), [LocalBound](../lean/ThresholdHC/AdditiveConfidence/LocalBound.lean) |
| Uniform component coefficient and confidence test | [ComponentPair](../lean/ThresholdHC/AdditiveConfidence/ComponentPair.lean), [ConfidenceRate](../lean/ThresholdHC/AdditiveConfidence/ConfidenceRate.lean) |
| Estimator and minimax conclusions for submeasures | [Full](../lean/ThresholdHC/AdditiveConfidence/Full.lean) |

## Verification and remaining work

The [native record](../results/additive-confidence-20261105/README.md)
checks 41 exact statements and 41 transitive axiom reports.
The [manuscript proof](../paper/v6/additive-confidence.tex) gives
the construction and constants.

The [sharper general-law confidence coefficient](ENTROPY_CONFIDENCE.md)
is now checked through a direct retained-entropy comparison with the
stopping program. It gives the coefficient $10^{-17}$ for every
known law. The generic fractional-submeasure theorem above retains
its component variance–null-work premises. The sharp quantile-factor
characterization retains its paper proof.
