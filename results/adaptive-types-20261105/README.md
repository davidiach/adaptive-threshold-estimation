# Selected-type information transfer

Proof checkpoint
[1f6a773aa1176a35cd83930d4d37b7251439c03e](https://github.com/davidiach/adaptive-threshold-estimation/commit/1f6a773aa1176a35cd83930d4d37b7251439c03e).

The native audit passes 48 exact statements and 48 transitive axiom
reports. All reports use only propext, Classical.choice and Quot.sound.
The closure contains 332 project modules, with 16 freshly compiled
modules and 316 unchanged inherited objects matched to prior published
hashes. The source, direct-dependency and object hashes were checked
against the proof commit. Every new compilation log is empty.

## Verified scope

- Independent label-dependent parameter laws give the exact physical
  observation-word law.
- Quarter-mixture likelihood factorization gives an exact KL hybrid sum.
- The local simulations charge each physical observation exactly once.
- Finite reference-work and null-work transfers have coefficients $8/3$
  and $16/3$, respectively.
- Countable labels and independent private randomization preserve the
  same prefix bound.
- Actual simulated paths obey the stopping policy. Finite endpoint work
  gives almost-sure stopping and reconstruction of the full transcript.
- The final $16/3$ theorem applies to component-specific known gap laws
  and conditional sign priors.
- Encoding type and coin index preserves each observation word and
  assigns every type infinitely many persistent labels.

The local policy-uniform Hellinger bound is an explicit premise. Its
derivation from a variance–null-work obstruction and the
fractional-submeasure confidence-localization theorem remain separate
formalization tasks.

## Reproduction

Run the portable audit from the repository root.

~~~sh
python tools/verify_typed_confidence.py
~~~

The [status record](status.json), [exact audit input](typed_confidence.lean)
and [kernel output](typed_confidence.log) preserve this checkpoint.
The numbered logs correspond to the 16 freshly compiled modules in the
status record. Current CI runs the same audit.

See the [proof map](../../docs/ADAPTIVE_TYPES.md),
[updated manuscript](../../paper/v6/builds/adaptive-types-20261105.pdf)
and [build record](../../paper/v6/builds/adaptive-types-20261105.json).
