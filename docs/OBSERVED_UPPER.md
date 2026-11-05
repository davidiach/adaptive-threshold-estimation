# Fresh-outer-state upper-bound transfer

This continuation connects the existing population estimator to the
observed-state experiment.

## Checked construction

For any deterministic observed-state sign model and its prescribed gap
law, the positive-gap submeasure has a measurable conditional sign
probability taking values in \([0,1]\) everywhere. Its density identity
gives the exact original population parameter law and threshold mean.

The selected-state policy assigns an independent uniform outer state to
each original coin label. Its policy follows the original observations,
and its output uses the original private seed and observation tape.

Run `python tools/verify_observed_upper.py` for the current component audit.

## Complete experiment transfer

The complete sampled-state transcript is now identified with the original
population experiment after discarding the auxiliary outer sequence.
Expected work, squared risk, RMS risk and failure probabilities transfer
exactly. The proof includes unbounded stopping and arbitrary measurable
private seeds.

One universal observed-state family now attains RMS radius
512 times the clipped modulus at one over the square root of the budget.
A second universal family attains confidence radius 8192 times the
clipped modulus at the confidence scale. Both charge actual observations
and are selected before the gap law and deterministic sign-cell model.

## Uniform-gap complexity

For gaps exactly uniform on \((0,1/4]\) and
\(0<\varepsilon\le e^{-16}\), both guarantees use expected work at most
\[
 131072^2\,\varepsilon^{-2}\log^2(1/\varepsilon)\log16.
\]
The confidence guarantee has failure probability \(1/16\).
The RMS guarantee has radius \(\varepsilon\).
Together with the [continuous-magnitude lower bounds and regularity](CONTINUOUS_OBSERVED.md),
these complete the two-sided observed-state complexity results.

The full audit checks 21 exact statements and 42 transitive axiom reports.
