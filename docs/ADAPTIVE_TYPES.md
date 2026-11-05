# Adaptive-type information transfer

The coefficient $16/3$ holds for the full observable experiment with
adaptive choice of component types, persistent revisits, independent
private randomization, countably many coin labels and unbounded stopping.

For each component, assume a single pair of conditional sign priors,
both bounded by $1/2$, satisfies the local null-work Hellinger inequality
for every capped observable single-coin procedure with any independent
auxiliary randomness. If the quarter-smoothed reference law uses at most
$B$ expected observations and the opposite endpoint has finite expected
work, the complete transcript KL is at most $(16/3)KB$.

## Proof structure

| Step | Native proof |
|---|---|
| Independent heterogeneous parameter laws and exact observation words | [ParameterPopulation](../lean/ThresholdHC/TypedConfidence/ParameterPopulation.lean) |
| Product likelihoods and exact quarter-mixture KL hybrids | [Factorization](../lean/ThresholdHC/TypedConfidence/Factorization.lean), [ParameterHybrid](../lean/ThresholdHC/TypedConfidence/ParameterHybrid.lean) |
| Every physical observation charged exactly once | [ParameterWork](../lean/ThresholdHC/TypedConfidence/ParameterWork.lean), [WorkLaw](../lean/ThresholdHC/TypedConfidence/WorkLaw.lean) |
| Finite reference-work coefficient $8/3$ and null-work coefficient $16/3$ | [FiniteTransfer](../lean/ThresholdHC/TypedConfidence/FiniteTransfer.lean), [NullTransfer](../lean/ThresholdHC/TypedConfidence/NullTransfer.lean) |
| Sign-prior mixtures and uniform local premise | [PriorMixture](../lean/ThresholdHC/TypedConfidence/PriorMixture.lean), [LocalBound](../lean/ThresholdHC/TypedConfidence/LocalBound.lean) |
| Horizon-dependent likelihood ratio, exact countable law and private-seed integration | [LikelihoodRatio](../lean/ThresholdHC/TypedConfidence/LikelihoodRatio.lean), [CountablePopulation](../lean/ThresholdHC/TypedConfidence/CountablePopulation.lean), [SeededTransfer](../lean/ThresholdHC/TypedConfidence/SeededTransfer.lean) |
| Actual path validity, almost-sure stopping and entropy reconstruction | [PathValidity](../lean/ThresholdHC/TypedConfidence/PathValidity.lean), [StoppedTransfer](../lean/ThresholdHC/TypedConfidence/StoppedTransfer.lean) |
| Final sign-law theorem and adaptive type-label encoding | [SignTransfer](../lean/ThresholdHC/TypedConfidence/SignTransfer.lean), [Labels](../lean/ThresholdHC/TypedConfidence/Labels.lean) |

For $k$ types, label $(j,i)$ is encoded as $jk+i$. Every type has an
infinite supply of labels, and revisits preserve the same coin.
The encoding theorem identifies the physical observation words exactly.

The bounded-horizon proof restricts to the finitely many labels its
decision tree can address. The likelihood ratio is bounded by $3^n$,
where $n$ is the observation horizon, even when labels are arbitrarily
large. Local work is measured under the same reference law throughout.

## Verification and remaining work

The [native record](../results/adaptive-types-20261105/README.md) checks
48 exact statements and 48 transitive axiom reports over a 332-module
project closure. The [manuscript subsection](../paper/v6/typed-confidence.tex)
states the hypotheses and gives the full proof.

The local policy-uniform pair is an explicit premise of this transfer.
The [common-pair construction](COMMON_PAIRS.md) now derives it from a
general variance–null-work obstruction. The [fractional-submeasure
localization](ADDITIVE_CONFIDENCE.md) is also Lean-checked. The
[sharper general-law confidence coefficient](ENTROPY_CONFIDENCE.md)
is checked through a direct stopping-program comparison. The sharp
quantile-factor characterization retains its paper proof.
