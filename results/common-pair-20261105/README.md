# Quantitative common-pair construction

Proof checkpoint
[8cf32f7e4092929d46eb87ecbb67b1e231bbcaec](https://github.com/davidiach/adaptive-threshold-estimation/commit/8cf32f7e4092929d46eb87ecbb67b1e231bbcaec).

The native audit passes 40 exact statements and 40 transitive axiom
reports. All reports use only propext, Classical.choice and Quot.sound.
The project closure has 341 modules, with 18 freshly compiled modules
and 323 unchanged inherited objects matched to prior published hashes.
Source, direct-dependency and object hashes match the proof checkpoint.
All new compilation logs are empty.

## Verified scope

- Hellinger affinity under a common reference measure permits zero
  densities and singular Bernoulli endpoints.
- The capped canonical transcript has exactly the finite sufficient
  statistic's affinity.
- Half-regularization toward a positive constant prior fixes the
  categorical support.
- The resulting bounded observable score has bias at most
  $6\varepsilon$, variance at most $18n\varepsilon^2$ and the same
  stopping rule and physical work.
- A variance–null-work obstruction gives a policy-wise separated pair
  and a quantitative Hellinger constraint.
- Exact finite mixtures and compact convex minimax produce one pair
  for every capped policy, cap and independent auxiliary seed.
- The local coefficient is $42\gamma^2/J$ for
  $0<\gamma\le b/3$.
- The existing common-pair premise follows internally, giving the
  estimator and minimax confidence coefficient $1/128$.

The variance–null-work obstruction remains the theorem's quantitative
premise. Fractional-submeasure additive localization and its general-law
entropy-packing application remain separate formalization tasks.

## Reproduction

~~~sh
python tools/verify_confidence_localization.py
~~~

The [status record](status.json), [exact audit input](confidence_localization.lean)
and [kernel output](confidence_localization.log) preserve this checkpoint.
The numbered logs match the 18 newly compiled modules in the status
record. CI runs the same portable audit.

See the [proof map](../../docs/COMMON_PAIRS.md),
[updated manuscript](../../paper/v6/builds/common-pair-20261105.pdf)
and [build record](../../paper/v6/builds/common-pair-20261105.json).
