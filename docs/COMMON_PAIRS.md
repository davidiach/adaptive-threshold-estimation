# Common pairs from a variance–null-work obstruction

For every known gap law, including laws with an atom at $1/2$, the
policy-uniform common pair follows from the quantitative variance–null-work
obstruction. The local coefficient is $42\gamma^2/J$ for every
$0<\gamma\le b/3$. The same pair works for every capped local procedure,
every cap and every independent auxiliary seed.

The resulting confidence lower bound is
$128^{-1}\min\{b,\sqrt{J\log(1/\delta)/B}\}$ for actual observable
estimators and for the minimax confidence radius.

## Precise premise

The obstruction asserts that every capped bounded one-coin estimator
with uniform bias at most $b$ and variance at most $V$ on the half-prior
class satisfies $V\mathbb E_0T\ge J$. The theorem constructs the
common pair from this premise. The [native definition](../lean/ThresholdHC/ConfidenceLocalization/Obstruction.lean)
quantifies over actual measurable procedures and independent seed laws.

## Proof map

| Step | Native proof |
|---|---|
| Common-reference Hellinger identity with zero densities | [DensityAffinity](../lean/ThresholdHC/ConfidenceLocalization/DensityAffinity.lean) |
| Exact finite sufficient statistic and convex geometry | [StatisticGeometry](../lean/ThresholdHC/ConfidenceLocalization/StatisticGeometry.lean) |
| Midpoint parameter laws and constant-prior domination | [PriorMidpoint](../lean/ThresholdHC/ConfidenceLocalization/PriorMidpoint.lean), [PriorDomination](../lean/ThresholdHC/ConfidenceLocalization/PriorDomination.lean), [CappedMixture](../lean/ThresholdHC/ConfidenceLocalization/CappedMixture.lean) |
| Fixed support and score recentering | [StatisticSupport](../lean/ThresholdHC/ConfidenceLocalization/StatisticSupport.lean), [MixtureScore](../lean/ThresholdHC/ConfidenceLocalization/MixtureScore.lean) |
| Bounded observable estimator with bias $6\varepsilon$, variance $18n\varepsilon^2$ and unchanged work | [RegularizedObservation](../lean/ThresholdHC/ConfidenceLocalization/RegularizedObservation.lean), [CappedEstimator](../lean/ThresholdHC/ConfidenceLocalization/CappedEstimator.lean) |
| Power-affinity pair and quantitative policy-wise constraint | [PowerPair](../lean/ThresholdHC/ConfidenceLocalization/PowerPair.lean), [PolicyPair](../lean/ThresholdHC/ConfidenceLocalization/PolicyPair.lean) |
| Regularized geometry, seed/cap changes and exact policy mixtures | [RegularizedGeometry](../lean/ThresholdHC/ConfidenceLocalization/RegularizedGeometry.lean), [ObservationCongruence](../lean/ThresholdHC/ConfidenceLocalization/ObservationCongruence.lean), [PolicyAuxiliary](../lean/ThresholdHC/ConfidenceLocalization/PolicyAuxiliary.lean), [PolicyMixture](../lean/ThresholdHC/ConfidenceLocalization/PolicyMixture.lean) |
| One pair simultaneously for all policies and caps | [CommonPair](../lean/ThresholdHC/ConfidenceLocalization/CommonPair.lean) |
| Existing common-pair premise and the estimator/minimax confidence bounds | [ConfidenceRate](../lean/ThresholdHC/ConfidenceLocalization/ConfidenceRate.lean) |

The proof regularizes each prior halfway toward the positive constant
prior $\rho$. A score on that class can be recentered to estimate the
original target with twice the bias and variance bounds. This fixes the
finite observation support while preserving the physical acquisition
rule. Compactness and finite policy mixtures then place the pair before
the policy quantifiers.

## Verification and remaining work

The [native record](../results/common-pair-20261105/README.md) checks
40 exact statements and 40 transitive axiom reports over 341 project
modules. The [manuscript proof](../paper/v6/common-pair-confidence.tex)
states the hypotheses and construction.

Fractional-submeasure additive confidence localization, its general-law
entropy-packing application and the sharp quantile-factor formalization
remain in progress.
