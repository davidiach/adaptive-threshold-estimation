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
| [FractionalPrior](../lean/ThresholdHC/EntropyTailLower/FractionalPrior.lean) | Constructs admissible event priors of an exact rarity mass even when the gap law has atoms, and proves their population mean and second-moment identities. |
| [GeneralGoodGaps](../lean/ThresholdHC/EntropyTailLower/GeneralGoodGaps.lean) | Derives a measurable good set with exceptional mass at most `70 m` from actual uniform population guarantees on any probability space. It removes the old atomlessness restriction. |
| [PopulationAnnular](../lean/ThresholdHC/EntropyTailLower/PopulationAnnular.lean) | Derives the moment floor and conditional mean, moment, and work premises, then proves `rho * Gamma <= 33554432 * m * W0`. Each band must have mass at least `140 m`; this mass condition is still a premise. |
| [ActivationGate](../lean/ThresholdHC/EntropyTailLower/ActivationGate.lean) | Constructs an observable bounded gate, proves its stop is the minimum of the original stop and boundary/cap clock, treats ties as acceptance, bounds the stopped random walk, and charges gate work to actual original work. |
| [GateLikelihood](../lean/ThresholdHC/EntropyTailLower/GateLikelihood.lean) | Proves exact fair-word likelihood factorization and uniform factors between `exp(-12)` and `exp(12)` on the actual stopped prefixes at scale `a <= 1/4`. Both signs are covered through `abs d <= a`. This is a wordwise bound, not yet the full conditioning/renewal theorem. |
| [FairGateWork](../lean/ThresholdHC/EntropyTailLower/FairGateWork.lean) | Proves the fair stopped-walk square identity by finite predictable sums and next-flip independence, including arbitrary random seeds. Derives fair activation probability at most `2 a^2` times expected gate work, without an integrability or termination assumption on the original procedure. |

The supporting weighted-sign target and its dependency hashes were recorded
before accepting its proof in
[the new specification lock](../tools/entropy_tail_lower_specification_freeze.json).
The coefficient is conservative and is not the paper's sharper coefficient.
No existing specification, manuscript, or published evidence is changed.

## Remaining mathematical work

1. Transfer the checked wordwise likelihood factors to actual stopped-prefix
   laws and use them to compare gate probability and work under biased coins
   with the checked fair-law bounds. Implement rejection and restart
   on unused flips, and prove its renewal/work and moment identities. Derive
   the conditioned estimator's good-gap bounds, including saturation. Its
   conditioning does not preserve bias, so the population guarantee cannot
   simply be reused for the conditioned estimator.
2. Connect an arbitrary feasible finite certificate to the required one-coin
   guarantees and the gate construction.
3. Prove the deterministic selection and packing steps: split retained bands
   by scale and cost, allocate rarity across the families, and combine their
   lower bounds with the ordinary and ignored parts of the selection cost.
4. Handle arbitrary laws through canonical finite-prefix approximation,
   maintaining the original selection functional and global rarity budget.
5. Prove `CertificateLowerStatement`, apply the checked equivalence, and
   register `entropy_tail_lower` against the original frozen specification.
   Then assemble the two-sided entropy-tail and closed-quantile laws and run
   their full exact-type audits.

The certificate route can reuse the existing formal treatment of arbitrary
adaptive population algorithms. It does not make steps 1–4 automatic.

## Verification

Run the new audit from the repository root:

```sh
python tools/verify_entropy_tail_lower_components.py
python -m unittest discover -s tools -p 'test_entropy_tail_lower_components.py' -v
```

The default rebuilds the entire local dependency closure. With
`--cached-dependencies`, it rebuilds the thirteen supporting modules, records the source
hashes and reused local artifact hashes, and explicitly reports that a full
dependency rebuild was not performed. Both modes check nine exact types and
all 72 declaration roots, permitting only `propext`, `Classical.choice`,
and `Quot.sound`. Fresh logs and status go under
`.runtime/entropy-tail-lower-components/`; published historical records are
preserved. The success report always keeps `entropy_tail_lower_verified`,
`entropy_tail_law_verified`, and `closed_quantile_minimax_verified` false.
It also keeps `full_information_gate_verified` and
`gate_restart_renewal_verified` false.

The CI configuration builds the new modules and runs the supporting audit in
the existing stopping-program job. A configured job is not evidence of a CI
pass. Development is tracked in [draft PR #38](https://github.com/davidiach/adaptive-threshold-estimation/pull/38),
with the first audited checkpoint committed as `551c1b9`; consult the PR for
CI status at each later commit.

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

### Atomic population and bounded gate checkpoint, 1 November 2026

The cached-dependency audit passed in
`.runtime/entropy-tail-lower-components/20261101T132121990813Z/`: all twelve
supporting modules were rebuilt, all seven exact types checked, and all 56
declaration roots had only the permitted axioms. The closure contains 386
local modules, with 374 dependencies reused and hashed. The full 280-test
verifier suite, frozen-source check, and whitespace check passed.

This checkpoint proves the atomic population and bounded-prefix results in
the table. The activation probability, restart renewal, and final lower-bound
claims remain unverified; the audit records those limitations explicitly.

### Fair activation checkpoint, 1 November 2026

The cached-dependency audit passed in
`.runtime/entropy-tail-lower-components/20261101T132622305225Z/`: all thirteen
supporting modules were rebuilt, all nine exact types checked, and all 72
declaration roots had only the permitted axioms. The closure contains 387
local modules, with 374 existing dependencies reused and hashed. The nine
audit regression tests passed again after adding the new fair-probability
scope flag. This checkpoint adds the fair-law square identity and activation
bound; it does not establish biased-law transfer or restart renewal.
