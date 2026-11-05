# Observed-state verification

This development formalizes the finite-cell and continuous-magnitude
observed-state lower bounds in the consolidated manuscript.

## Verified components

The initial component audit checks the following results.

- A product prior on the deterministic cell signs has the exact weighted
  target mean and variance. A second-moment bound controls the probability
  that this target differs from its prior mean.
- Independent sign-symmetric noise converts a larger-gap Bernoulli
  observation into a smaller-gap observation with the same cell sign.
  The equality is checked for the actual probability measures.
- The finite-cell experiment uses independent Bernoulli tapes and the
  original adaptive path simulator, with arbitrary measurable private
  randomness. Its mixture is a probability law, and uniform work bounds
  for deterministic signs bound the mixture's expected physical work.
- The existing finite rounding grid gives an upward finite-range map.
  Its gap CDF is dominated by the original law, and its clipped modulus
  is at least half the original modulus.

Run `python tools/verify_observed_states.py` for the component audit.

## Remaining assembly

The finite experiment still needs its full transcript information bound,
the estimation-to-testing reduction, and the finite-partition construction.
The continuous-magnitude result also needs the adaptive noise simulation
and its exact work and observation-law identities. The full observed-state
theorems retain their paper-proof status while those steps are in progress.
