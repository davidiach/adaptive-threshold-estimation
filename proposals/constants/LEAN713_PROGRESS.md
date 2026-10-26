# Full 713 Lean development

The complete untruncated theorem is being formalized separately from the 33
original frozen targets. Its exact target is `FullBound713Statement` in
`lean/ThresholdHC/Uniform713/Specification.lean`; the new verifier records that
file's SHA-256 and checks the final theorem against that type when available.

The model permits any magnitude/sign law and a conditional observation kernel.
Observations are independent, measurable, [0,1]-valued, and have common mean
1/2 ± d. Thus the intended Bernoulli model is included. The only moment assumption
on the magnitude law is integrability of 1/d. The target includes square
integrability, integrable work, unbiasedness, and the strict product bound 713.
No classifier error, stopping-work, or estimator moment bound is assumed.

First component checkpoint:

- Derived both Hoeffding tails from independent bounded observations.
- Defined the actual capped dyadic classifier, including its tie convention.
- Proved measurability, the survival identity, and pathwise shared-tape work.
- Proved both infinite weighted geometric estimates, with constants 23 and 31.
- Constructed the geometric probability measure and independent sampled estimator.
- Proved the exact second-moment sum and the telescoping unbiasedness criterion.
- Added integration helpers for arbitrary parameter laws.

These components are machine-checked; the complete theorem is still in progress.
`python tools/verify_uniform713.py` builds the registered modules and independently
audits every registered proof root. Its JSON explicitly distinguishes a valid
component checkpoint from `full_theorem_complete`. Use `--require-complete` to
reject partial checkpoints. Only `propext`, `Classical.choice`, and `Quot.sound`
are accepted. Original frozen files and their 60/60 result are preserved.
