# Information inequalities for the all-law time-uniform lower bound

The proof checkpoint is [0544b2a](https://github.com/davidiach/adaptive-threshold-estimation/commit/0544b2af17c9f12406e590fdafdaffa54494b38e).

The [native record](status.json) checks 15 exact statements and 15 transitive axiom reports. All four fresh compiler logs are empty. The closure contains 332 project modules, including 328 reused dependencies with published matching object hashes. Source, direct-dependency and object identities were verified. The only reported axioms are Lean's standard `propext`, `Classical.choice` and `Quot.sound`.

The [audit input](anytime_lower.lean) and [raw output](anytime_lower.log) cover central prior-family information/work scaling, quarter-smoothing inversion, physical prefix work, admissibility, target separation, observable prefix KL, posterior bounds and Lipschitz continuity, and one-flip Bernoulli KL.

Run `python tools/verify_anytime_lower.py` for the native audit. Run `python tools/verify_anytime_lower_profiles.py` for 32,768 exact rational profile comparisons on 16 finite atomic examples, including grid endpoints. Those examples are regression checks, not a universal proof.

The [complete all-law lower bound](../../docs/TIME_UNIFORM_LOWER.md) remains a paper proof. The sequential testing lemma, infinite-moment profile construction, adaptive acquisition transfer and asymptotic comparisons are not covered by this Lean audit. The theorem concerns a deterministic envelope at fixed law, rarity and confidence, infinitely often as the physical budget tends to infinity.
