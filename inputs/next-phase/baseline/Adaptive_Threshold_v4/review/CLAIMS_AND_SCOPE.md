# Assumptions and unresolved questions

## Observation model
Fresh coins are independent. Given a coin's fixed latent P, its observations are independent Bernoulli(P). D=|P−1/2| is strictly positive almost surely but may have arbitrary law on (0,1/2]. Algorithms can revisit, interleave, and stop adaptively. The comparison benchmark uses uniformly bounded expected observation count over all measurable conditional sign functions q.

The lower bound remains valid with individual magnitudes disclosed, and even with selected fresh magnitudes (q is then defined over the full interval). It does not assume per-coin deterministic query bounds. Extra task labels carrying sign information are not included unless covered by the explicit observable-state construction.

## Calibration
Calls are independent, with finite value variance and bounded nonnegative cost. Positive mean cost is required. Value and cost may be dependent within a call. Marking probability is observed cost divided by the deterministic per-call cap. Production values are independent of all pilot data and markers. No pilot-output reuse is permitted in the proof.

## Uniformity
Risk is maximized over q at fixed μ; it is not instance optimality at each (μ,q). Unbiased impossibility is likewise uniform over q, not a statement about a single known distribution. The hard priors stay near q=1/2. Rare-event localization is unresolved.

## Smoothness and nested simulation
Smoothness of the density of latent P is not regularity of the observable regression function. Smooth-density proof uses a0=1/4. The continuous observed-state subclass has arbitrarily many cells; it is not an asymptotic result for a fixed finite partition. The map of magnitudes and partition can be disclosed without eliminating the lower bound. Conditional signs remain unknown.

## Not proved here
- A θ-localized arbitrary-margin law for rare events.
- A deterministic cap or high-probability tail bound on total work at the same optimal rate.
- A numerical confidence radius computable from finite data uniformly over all unknown margin laws.
- Optimal universal upper constants or exact optimal variance–work product for every law.
- Analogous smoothness lower bounds for fixed analytic or Gevrey classes.
- Robustness to dependence between fresh tasks, probability drift, or misspecified observation noise.
- Practical performance gains on real AI-verifier or financial-simulation data.
- Publication priority or independent human proof certification.
