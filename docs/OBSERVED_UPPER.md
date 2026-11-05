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

## Remaining transfer

The proof must identify the complete sampled-state transcript with the
population experiment, then transfer actual expected work, RMS risk and
confidence guarantees. The matching observed-state upper bounds retain
their paper proofs while this connection is completed.
