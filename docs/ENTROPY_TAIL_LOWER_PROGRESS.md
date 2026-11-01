# Entropy-tail lower-bound progress

This additive development starts from main commit
`4553d9e2207cbc3534f434da211828a50c9f9f1d`. It supplies supporting lemmas for
the missing statistical lower bound. It does **not** prove
`EntropyTailLowerStatement`, the two-sided entropy-tail law, or the matching
closed-quantile lower bound. The existing eight-target registry remains at
six proved targets.

## New statements and proof route

| Module | Result and scope |
|---|---|
| [Specification](../lean/ThresholdHC/EntropyTailLower/Specification.lean) | A frozen weighted single-coin sign-testing target, with coefficient 4096. The gaps are in `(0,1/128]` and successive gaps differ by at least a factor of two. Weights are arbitrary and nonnegative, including zero; they need not sum to one. |
| [WeightedOverlap](../lean/ThresholdHC/EntropyTailLower/WeightedOverlap.lean) | A pathwise bound of 32768 on exponentially weighted actual stopping windows. It allows nontermination under the fair-coin law. |
| [WeightedSign](../lean/ThresholdHC/EntropyTailLower/WeightedSign.lean) | Derives weighted entropy from the window bound, fair-law change of measure, and the existing single-gap work floor. Only negative-sign expected work must be finite; both testing errors must be at most 1/10. |
| [WeightedEstimation](../lean/ThresholdHC/EntropyTailLower/WeightedEstimation.lean) | Converts a real-valued stopped procedure with separated means and bounded second moments to the sign-testing bound through actual independent restarts. The cost multiplier is the number of restarts. |
| [AnnularWork](../lean/ThresholdHC/EntropyTailLower/AnnularWork.lean) | Selects good points with controlled average work under an arbitrary finite measure, sums disjoint band costs, and proves annular sign entropy with coefficient 16384. Every band must retain at least half its mass in the measurable good set. |
| [AnnularEstimation](../lean/ThresholdHC/EntropyTailLower/AnnularEstimation.lean) | Combines annular averaging and the estimator reduction. Bands lie in `(b/2,b]`, with successive endpoints separated by a factor of four. Moment, mean-separation, integrability, and good-set premises remain explicit. |
| [CertificateReduction](../lean/ThresholdHC/EntropyTailLower/CertificateReduction.lean) | Proves that the unchanged canonical lower target is equivalent to a lower bound uniform over all feasible positive-cap finite certificates. The reverse implication loses a factor of 16, using the existing attained certificate and risk comparison. The finite-certificate lower bound is an obligation, not a proved premise. |

The supporting weighted-sign target and its dependency hashes were recorded
before accepting its proof in
[the new specification lock](../tools/entropy_tail_lower_specification_freeze.json).
The coefficient is conservative and is not the paper's sharper coefficient.
No existing specification, manuscript, or published evidence is changed.

## Remaining mathematical work

1. Derive the moment and mean-separation premises of the annular estimator
   theorem from an arbitrary feasible finite certificate. This needs the
   scale-dependent activation/restart gate and quantitative control of the
   bad-gap mass, including the saturation case.
2. Prove the deterministic selection and packing steps: split retained bands
   by scale and cost, allocate rarity across the families, and combine their
   lower bounds with the ordinary and ignored parts of the selection cost.
3. Handle arbitrary laws through canonical finite-prefix approximation,
   maintaining the original selection functional and global rarity budget.
4. Prove `CertificateLowerStatement`, apply the checked equivalence, and
   register `entropy_tail_lower` against the original frozen specification.
   Then assemble the two-sided entropy-tail and closed-quantile laws and run
   their full exact-type audits.

The certificate route can reuse the existing formal treatment of arbitrary
adaptive population algorithms. It does not make steps 1–3 automatic.

## Verification

Run the new audit from the repository root:

```sh
python tools/verify_entropy_tail_lower_components.py
python -m unittest discover -s tools -p 'test_entropy_tail_lower_components.py' -v
```

The default rebuilds the entire local dependency closure. With
`--cached-dependencies`, it rebuilds the seven new modules, records the source
hashes and reused local artifact hashes, and explicitly reports that a full
dependency rebuild was not performed. Both modes check two exact types and
all 14 new declaration roots, permitting only `propext`, `Classical.choice`,
and `Quot.sound`. Fresh logs and status go under
`.runtime/entropy-tail-lower-components/`; published historical records are
preserved. The success report always keeps `entropy_tail_lower_verified`,
`entropy_tail_law_verified`, and `closed_quantile_minimax_verified` false.

The CI configuration builds the new modules and runs the supporting audit in
the existing stopping-program job. A configured job is not evidence of a CI
pass; new branch CI has not been run by this local development.

### Local checkpoint, 1 November 2026

The cached-dependency audit passed in
`.runtime/entropy-tail-lower-components/20261101T130332710988Z/`: all seven new
modules were rebuilt, both exact types checked, and all 14 declaration roots
had only the permitted axioms. Its 374 reused local dependency sources match
the `entropy-tail-integrated` cache checkout byte for byte; this was not a
fresh rebuild of those dependencies. The audit records hashes of the reused
local artifacts as well as the source closure.

The existing 271 verifier tests, nine new audit-guard tests, and 198 toolkit
tests passed. The frozen-source check, project-wide proof-escape scan,
documentation file links, and whitespace checks also passed. The canonical
`verify_entropy_tail.py --require-complete` check still correctly fails,
naming `entropy_tail_lower` and `entropy_tail_law` as unproved.
