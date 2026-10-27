# Independent review of the new paper arguments

**Status: independent agent paper review, not a Lean proof or external referee
endorsement.** The reviewer did not author the reviewed arguments. No
mathematical defect was found in the claims below under their stated scope.

## Uniform product bound 713

Reviewed `constants/UNIFORM_PRODUCT_BOUND.md` and `constants/BIAS_AUDIT.md`
against `../constants/evaluator.py` and the supplied v4 paper's classifier,
geometric-level, and work definitions. The proof concerns `(k1,k2)=(1/4,1)`.

- The one-sided error union bound is valid despite adaptive stopping: each
  potential stopping event is bounded using its fixed prefix. The bound
  `x^2 exp(-2x) <= exp(-2)` holds on every positive x, so the strengthened
  all-scale error envelope and `min(1,3x^-2)` difference envelope follow.
- Splitting the second-moment geometric sum before/after `2^l(d')^2=1`
  gives the claimed constant. When the finite cutoff precedes the split,
  only the prefix is present, which supplies the required `sqrt(2^L)` branch.
- The work calculation correctly uses a one-sided survival deviation.
  Its constant is `1/4+2+169/36=125/18`; the logarithmic coefficient is
  `338/49`. Both are below seven. The deterministic cap supplies the other
  branch of `m_N`.
- On the same observation stream and with the same threshold parameters,
  the coarse threshold is smaller before its cap. Thus
  `tau_coarse <= tau_fine` pathwise, even when their eventual decisions differ.
  Using the maximum rather than the sum is justified by the evaluator's
  actual work model. The geometric work sum is below `31 min(sqrt(N),1/d)`.
- The infinite-estimator conclusion is valid when `I=E[1/D]` is finite.
  For explicit justification, take the same independently drawn geometric
  level J and tape for Y and every Y_L. Then
  `E[(Y-Y_L)^2] = sum_{l>L} E[Delta_l^2]/p_l -> 0`.
  The finite second-moment sum therefore gives L2, hence L1, convergence;
  telescoping and the vanishing classifier error give unbiasedness.

The exact rational comparisons in `uniform_constant_checks.py` passed on
review. These checks verify arithmetic only. At the time of this review, the full
probability argument had paper-proof status. It was subsequently formalized as
[`ThresholdHC.Uniform713.full_bound_713`](../lean/ThresholdHC/Uniform713/FullBound.lean);
see the [complete kernel audit](../results/uniform713_status.json). The constant
713 is an upper bound, not an optimum, and does not identify the finite-grid proxy
with a universal value.
It does not apply to the direct-real heuristic classifier in the benchmark.

## Counterexample for the finite-grid winner

The all-tails event through prefix 128 has probability `(2/5)^128` for the
positive coin with d=1/10. At cap `2^97`, the `(1/4,1/2)` threshold is strictly
below 1/2 by that prefix; any earlier stop on the same event is also negative.
The event therefore lower-bounds misclassification probability. The exact
comparison against `10000/2^194` exceeds 2907, as the rational check confirms.
This is a valid off-grid counterexample to the stated uniform bias bound.
It does not invalidate the finite-grid scorer's reported acceptance, and does
not itself determine the winner's alternative asymptotic bias rate.

## Unknown-rarity adaptation obstruction

The argument in [TRACK_D.md](../docs/process/TRACK_D.md) is sound for its fully uniform formulation.
For each fixed budget, using the same estimator for every positive rarity
bound forces zero second moment at theta=0. With `0<d<1/2`, every feasible
finite binary observation history has positive likelihood under all constant
sign priors in the stated range. Conditional on the common independent random
seed, likelihood ratios on each finite stopping-time event are finite and
positive. Almost-sure termination extends mutual absolute continuity to the
full stopped transcript, so zero output at theta=0 transfers to theta=1/4.
The contradiction for sufficiently large budgets follows.

Both exclusions matter: deterministic coins at d=1/2 and estimators supplied
with rho are outside this argument. An additive error floor, a positive lower
bound on rho, or restricted parameter ranges can avoid the obstruction.
The result does not resolve distribution-blind adaptation when rho is known,
nor does this review assert novelty.
