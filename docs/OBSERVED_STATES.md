# Observed-state lower bounds

## Finite-cell theorem

The finite-cell observed-state obstruction is Lean-checked for every gap
law, every scale \(0<h\le1/2\), and \(0<\delta\le1/8\).
The construction gives a finite measurable partition of the uniform
state space and a deterministic Bernoulli model for every cell-sign
array. Its magnitude CDF is bounded by the original gap CDF, and its
target separation satisfies \(\Delta\ge\omega_\mu(h)/8\).

Every measurable selected-state algorithm with error at most \(\Delta/4\)
and failure probability at most \(\delta\) throughout this family has
worst-case expected work at least
\[
 \frac{225}{128h^2}\operatorname{kl}(1-2\delta,2\delta).
\]
Queries may choose any point, revisit states, and interleave cells.
The private seed can include all free outer samples. The experiment
charges one physical observation for each active query.

## Proof map

- Rounding raises small gaps and applies the existing finite grid.
  The resulting upward map preserves at least half the clipped modulus.
- OuterMeasure, Labels, Design, and Construction realize the
  gap law and an independent replication index as measurable functions
  of a uniform state. Their fibers give the finite cells.
- Targets and Replication prove the product-prior target mean,
  variance, concentration, and a sufficient finite replication count.
- Experiment and Realization identify the actual independent-tape
  Bayes transcript with the adaptive finite-prefix model.
- Information, Testing, and FiniteLower derive the stopped
  information bound and the exact testing constant.
- StateModel, Mean, and Finite connect arbitrary point queries,
  conditional expectations, the threshold target, and the full theorem.
- Garbling identifies a smaller-gap observation as a larger-gap
  Bernoulli observation with independent noise.

Run `python tools/verify_observed_states.py` for 22 exact statements and
58 transitive axiom reports. The audit checks the full theorem and its
experiment connections.

The construction uses the second-moment condition
\(M^{-1}\le\delta\Delta^2/16\). The paper's Hoeffding-based replication
count remains a separately proved bound.

## Continuous magnitudes

The [continuous-magnitude lower bounds and regularity](CONTINUOUS_OBSERVED.md)
and the [fresh-state upper-bound transfer](OBSERVED_UPPER.md) are now
Lean-checked, completing both two-sided complexity rates.
