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

## Completed theorem

The [full theorem](../lean/ThresholdHC/SmoothDensity/Full.lean) checks the
class-wide two-sided expected complexity and uniform unbiased impossibility.
For each fixed finite derivative order, one sufficiently large finite bound
defines a class with complexity proportional to
`ε⁻² log²(1/ε) log(1/δ)`, for sufficiently small positive accuracy and
`0 < δ ≤ 1/4`. The upper coefficient is `(65536 M)²`.

The class is represented in the original gap/sign experiment by equality
against every bounded measurable function of the latent Bernoulli parameter.
The proof identifies that law with the existing independent-tape construction
and identifies its threshold probability with the original sign mean.

The upper family is selected before the density. The lower bound permits
arbitrary measurable private randomness, adaptive revisits, interleaving and
unbounded stopping. The unbiased impossibility applies to estimators with
uniform finite variance and uniform finite expected work throughout the class.

## Proof map

| Modules | Result |
|---|---|
| Rational, Perturbation, Bump, Densities | Uniform derivatives and normalized smooth densities |
| Separation, Scale | Logarithmic separation and the accuracy-dependent scale |
| GapLaw, Representation, LatentLaw | Common gap law and the original parameter law |
| Information, SymmetricInformation | Actual expected-work information bounds |
| Envelope, Upper | Density-to-CDF bound and a law-independent upper family |
| Lower, Unbiased, Full | Both complexity bounds and unbiased impossibility |

All modules are in [SmoothDensity](../lean/ThresholdHC/SmoothDensity/Full.lean).
The [native audit](../results/smooth-density-20261105/README.md) checks
15 independent exact statements and 46 transitive axiom reports.
[Appendix W](../paper/v6/appendix-smooth-density.tex) supplies the updated
paper proof. The [149-page manuscript](../paper/v6/builds/smooth-density-20261105.pdf)
includes that appendix and the revised verification scope.
