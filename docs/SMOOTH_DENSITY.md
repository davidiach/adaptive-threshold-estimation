# Smooth-density verification

This development formalizes the smooth-density robustness theorem in the
consolidated manuscript. The completed theorem concerns a fixed finite-order
derivative bound. The density pair changes with the requested accuracy.

## Verified construction

The current exact-type and transitive-axiom audit checks the following results.

- The rational profile `x / (1 + x²)` has derivatives bounded by `k!`.
- The perturbation `t^s / 8 * profile(x / t)` has derivatives through order
  `s` bounded by `k! / 8`, uniformly for `0 < t ≤ 1`.
- A fixed even normalized bump produces nonnegative, normalized, infinitely
  differentiable densities supported in `[1/4, 3/4]`.
- For each `s`, one finite constant bounds all derivatives through order
  `s` for both densities at every smoothing scale.
- The probabilities above the centered threshold differ by at least
  `t^(s+1) log(1/t) / 8` when `0 < t ≤ 1/64`.
- The original randomized adaptive experiment has KL divergence at most
  `(128/225) h² B` for a local sign pair satisfying
  `0 ≤ η ≤ 1/8` and `dη ≤ h/8`. Only expected work under the plus law is
  required. Arbitrary revisits, interleaving and unbounded stopping are allowed.
- An explicit positive accuracy cutoff and scale give separation above
  `2ε` with `t^(s+1) = 64(s+1) ε / log(1/ε)`.

The audit command is `python tools/verify_smooth_density.py`.

## Remaining assembly

The initial checkpoint verifies the analytic construction and the local
information bound separately. Connecting the constructed density pair to the
original latent-parameter law, completing the class-wide two-sided complexity
theorem, and proving the smooth-class unbiased impossibility remain in progress.
The manuscript retains its paper-proof status for the full smooth-density claim
until that assembly and its exact-type audit are complete.

The historical generated theorem and its source files are preserved.
