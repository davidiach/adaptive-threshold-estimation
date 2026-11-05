# Continuous-magnitude observed-state proof

This continuation addresses the continuous-magnitude proposition after the
[finite-cell theorem](OBSERVED_STATES.md).

## Adaptive simulation

A point query in a cell with actual gap \(d\) is simulated using one
observation from a fixed cell coin with larger gap \(b\), followed by
independent sign-symmetric noise of probability \((1-d/b)/2\).
The fixed cell coin shares the original persistent hidden sign.

The checked components establish the following results.

- The transformation has exactly the requested Bernoulli law for either sign.
- The history decoder uses only preceding transformed observations.
- Decoding preserves the stopping pattern and the total physical work on every tape.
- The reduced policy and output are measurable. The output sees the original seed and transformed tape.
- Estimation error and expected work transfer exactly to the reduced experiment.
- The finite-cell testing bound transfers to the simulated variable-gap law.
- The recursive execution matches the decoded finite-population simulator.
- Extracting the next observation and noise value leaves all unused randomness independent with its original product law.

Run `python tools/verify_continuous_observed.py` for the current component audit.

## Physical experiment and moments

The full finite-prefix law is now identified with the ordinary fresh
Bernoulli rule at every adaptively selected point. It retains the original
private seed jointly with the observations and determines the complete
infinite transcript law uniquely.

The variable-gap theorem constructs a finite sign-cell design with exactly
any prescribed gap law and separation at least one eighth of its clipped
modulus. The exact confidence lower bound applies to every physical law
with those ordinary observation probabilities.

For gaps at most one quarter, the conditional variance is at least three
quarters, the centered observation is bounded by three halves, and its
normalized central moment of every real order q at least zero is bounded
by three to the power q/2. These are checked directly for the actual
binary observation law.

## Remaining proof

The full continuous-magnitude proposition still needs the uniform gap-law
construction with its pointwise cutoff, the normalized-magnitude density
check, and the matching complexity and RMS statements.

The external assumptions require a density of the conditional mean's
absolute value divided by its conditional standard deviation that is
bounded near zero, and a uniformly bounded normalized conditional
central moment of some finite order greater than two. These are
Assumptions 2.1 and 2.4 in the authors' paper. [Giles–Haji-Ali](https://arxiv.org/pdf/1802.05016)
