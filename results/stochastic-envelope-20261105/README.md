# Distribution-blind estimation under a stochastic envelope

Write $I=\int d^{-1}\,d\mu$. The actual gap law may be any probability
law whose CDF is below the reference CDF at every positive cutoff.
The original estimator sees its private seed and purchased flips. Its family
can be chosen before either law.

| Statement | Lean-checked guarantee |
|---|---|
| [RMS and confidence](../../lean/ThresholdHC/Envelope/Minimax.lean) | At $B\ge1$ the minimax RMS coefficients on the reference modulus are $1/64$ and $512$. At failure level $0<\delta\le1/4$ the confidence coefficients are $15/(256\sqrt2)$ and $8192$ at the confidence scale. |
| [Unbiased estimation](../../lean/ThresholdHC/Envelope/Unbiased.lean) | A single estimator has finite uniform variance and work exactly when $I$ is finite. The minimax product of separate uniform bounds is between $I^2/16$ and $713I^2$. The upper construction has variance at most $23I$ and expected work at most $31I$. |
| [CDF comparison](../../lean/ThresholdHC/Envelope/Moments.lean) | Integrating superlevel probabilities compares the two clipped moduli and transfers inverse-moment integrability, including for laws with atoms. |

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/eb5a2ffdb9af6a52dc47cd2aa5a31a1dfb21ad16),
the [native record](status.json) covers 253 modules. The three new
modules compiled without warnings. Of 250 inherited objects, 214 match
earlier published hashes and 36 have their first recorded hashes here.
[Six exact statements](stochastic_envelope.lean) passed with
[eleven transitive axiom reports](stochastic_envelope.log) using only the
standard allowed axioms. Run `python tools/verify_stochastic_envelope.py`
with the pinned toolchain. The rare-event power-margin envelope has an
additional rarity parameter and is a separate theorem.
