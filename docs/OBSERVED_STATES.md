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

## Finite-cell information and testing

The next checkpoint identifies the full Bayes transcript law of the concrete
independent-tape experiment. It proves the information bound from uniform
expected work over deterministic sign arrays and derives the exact lower
coefficient `225/(128h²)` multiplying `kl(1−2δ,2δ)`.

The testing theorem assumes an explicit finite design with separation `Δ`
and squared target weights at most `δΔ²/16`. The replication lemmas prove
that sufficiently many copies satisfy this concentration requirement.
This construction uses a second-moment cell-count bound.

## Remaining assembly

The observed-state results still need the complete finite-partition
construction. The continuous-magnitude result also needs the adaptive noise
simulation and its exact work and observation-law identities. The full
observed-state theorems retain their paper-proof status while those steps
are in progress.
