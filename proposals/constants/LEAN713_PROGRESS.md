# Full 713 Lean development

The complete untruncated theorem is proved separately from the 33
original frozen targets. Its exact target is `FullBound713Statement` in
`lean/ThresholdHC/Uniform713/Specification.lean`; the new verifier records that
file's SHA-256 and checks `full_bound_713` against that exact type.

The model permits any magnitude/sign law and a conditional observation kernel.
Observations are independent, measurable, [0,1]-valued, and have common mean
1/2 ± d. Thus the intended Bernoulli model is included. The only moment assumption
on the magnitude law is integrability of 1/d. The target includes square
integrability, integrable work, unbiasedness, and the strict product bound 713.
No classifier error, stopping-work, or estimator moment bound is assumed.

The checked proof covers:

- Derived both Hoeffding tails from independent bounded observations.
- Defined the actual capped dyadic classifier, including its tie convention.
- Proved measurability, the survival identity, and pathwise shared-tape work.
- Derived the classifier's error and expected-work envelopes for both signs.
- Proved both infinite weighted geometric estimates, with constants 23 and 31.
- Proved the finite-cap envelope refinements involving `min(sqrt(2^L),1/d)`.
- Constructed the geometric probability measure and independent sampled estimator.
- Proved the exact second-moment sum and the telescoping unbiasedness criterion.
- Added integration helpers for arbitrary parameter laws.
- Assembled the strict product inequality and proved the model satisfiable by
  a concrete Bernoulli(1) example.

The first component checkpoint `8a435ec` audited 86 roots while explicitly
recording that the full theorem was incomplete. The complete development now
audits 130 public proof roots. `python tools/verify_uniform713.py --require-complete`
builds the modules, independently audits every root, and requires the final proof
to inhabit the recorded target type. CI also requires completion. Only
`propext`, `Classical.choice`, and `Quot.sound` are accepted. Original frozen
files and their 60/60 result are preserved.

For direct use in Lean, import `ThresholdHC.Uniform713`. The main declaration is
`ThresholdHC.Uniform713.full_bound_713`. The helper `uniformWork_eq_coupled`
identifies the cost in that theorem with the actual maximum of fine/coarse
stopping costs on the shared tape. The final proof contains no assumed
concentration, error, work, second-moment, or unbiasedness bounds.

Checkpoint `852690a` passed the complete guard on Windows and in the independent
[Linux CI run](https://github.com/davidiach/threshold-hillclimb/actions/runs/40414013439).
Both CI jobs succeeded, including all 130 roots, the original frozen targets,
and the numerical/provenance checks. GitHub attributes both new proof
checkpoints to `davidiach`; earlier history was preserved.
