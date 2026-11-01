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
| [GateMeasure](../lean/ThresholdHC/EntropyTailLower/GateMeasure.lean) | Transfers the likelihood factors to the actual seeded stopped-transcript laws, event probabilities, and nonnegative observables. In particular, fair activation is at most `2 exp(12) a^2` times the original expected work under any coin with `abs(p-1/2) <= a <= 1/4`, retaining infinite work honestly. |
| [GatedOutput](../lean/ThresholdHC/EntropyTailLower/GatedOutput.lean) | Masks the output by the observable gate decision at the original stopping time, with no extra flips. Proves that the squared masked mean is bounded by activation probability times the original second moment. |
| [FiniteAverageProcedure](../lean/ThresholdHC/EntropyTailLower/FiniteAverageProcedure.lean) | Constructs actual finite averaging on successive unused flips of the same coin. Proves its independent output law, exact mean and work identities, and second-moment bound, with the needed finiteness assumptions explicit. |
| [GateAverage](../lean/ThresholdHC/EntropyTailLower/GateAverage.lean) | Uses `ceil(1/p)` masked runs, where `p` is fair activation. For `p > 0`, bounds moments by `(1 + exp(12)) p` times original moments and work by `2/p` times original work. Positivity of fair activation is still a premise. |
| [PopulationGateAverage](../lean/ThresholdHC/EntropyTailLower/PopulationGateAverage.lean) | Integrates the fixed-repeat bounds over arbitrary probability laws, including atoms. From the original uniform capped guarantee and positive activation, obtains a smaller uniform moment bound, finite actual work, and the population moment/work tradeoff. It does not assert the original bias guarantee for the transformed estimator. |
| [EarlyLikelihood](../lean/ThresholdHC/EntropyTailLower/EarlyLikelihood.lean) | Bounds the difference between the two sign likelihoods on the actual gate prefix by `8 exp(12) abs(d) abs(S_stop)`. This density bound still needs integration against the early output. |
| [EarlyOutput](../lean/ThresholdHC/EntropyTailLower/EarlyOutput.lean) | Constructs the observable early output at the bounded gate time, proves its moment is no larger than the original moment, and proves the exact early-plus-masked output and mean decompositions. |
| [EarlyMean](../lean/ThresholdHC/EntropyTailLower/EarlyMean.lean) | Integrates the actual stopped-prefix densities, proving the early sign-mean difference squared is at most `64 exp(48) a^2 M0 W0`. From the original capped population guarantee, symmetric signs, and `64 exp(48) a^2 m W0 <= 1/16`, derives positive fair activation. |
| [GatedGoodGaps](../lean/ThresholdHC/EntropyTailLower/GatedGoodGaps.lean) | Under the stronger small-work condition with right side `1/64`, derives positive activation and actual good gaps for the finite-average estimator. Their excluded mass is at most `64 mZ + 4 rho`. The transformed bias guarantee is not assumed. |

The supporting weighted-sign target and its dependency hashes were recorded
before accepting its proof in
[the new specification lock](../tools/entropy_tail_lower_specification_freeze.json).
The coefficient is conservative and is not the paper's sharper coefficient.
No existing specification, manuscript, or published evidence is changed.

## Remaining mathematical work

1. Absorb the additive rarity term in the gated good-set mass bound, then
   finish saturation and the choice of gate scale. The early-mean estimate,
   positive activation, and good-gap selection are now proved under explicit
   small scale/moment/work conditions. The construction derives transformed
   mean separation from the original guarantees; it does not assume that
   masking preserves the original bias guarantee.
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

### Finite-average reduction and its remaining premises

The formal development uses fixed repetition. Once fair activation `p > 0` is proved,
take `N = ceil(1/p)` independent full runs of the original procedure on
successive unused flips. Replace each output by `X = Y * 1_E`, and return
their average. Every run, including each rejected run, is charged in full.
The common repetition count depends on fair activation, not the hidden coin
parameter. For each fixed state with finite original work and second moment,
the checked bounds give

```text
E[average(X)^2] <= E[Y^2]/N + P(E) E[Y^2]
                <= (1 + exp(12)) p E[Y^2],
E[total work] = N E[T] <= 2 E[T]/p.
```

The first line uses independent averaging and the masked-mean square bound.
Averaging preserves `E[Y * 1_E]`; the early-output mean estimate supplies
the resulting mean-separation bound. The construction reuses the existing
[finite-average identities](../lean/ThresholdHC/BlindUpper/ProductionAverage.lean)
and [actual same-coin restart laws](../lean/ThresholdHC/CriticalEntropy/RepeatedRestart.lean).
Population integration now gives the corresponding uniform moment bound
`mZ = (1 + exp(12)) p m` and
`mZ W0Z <= 2 (1 + exp(12)) m W0`. Combining this with the activation/work
bound gives `mZ <= 2 exp(12) (1 + exp(12)) a^2 m W0`. These statements
assert moments and work, not transformed bias. The early-mean estimate now
derives `p > 0` when the symmetric population parameters lie within scale
`a` of the fair parameter and `64 exp(48) a^2 m W0 <= 1/16`.
With right side `1/64`, the transformed estimator has a measurable good set
whose excluded mass is at most `64 mZ + 4 rho`. Absorbing the additive rarity
term and completing saturation remain before the full gate reduction.
Rejection-loop renewal has not been formalized and is not used by this
fixed-repeat construction.

## Verification

Run the new audit from the repository root:

```sh
python tools/verify_entropy_tail_lower_components.py
python -m unittest discover -s tools -p 'test_entropy_tail_lower_components.py' -v
```

The default rebuilds the entire local dependency closure. With
`--cached-dependencies`, it rebuilds the twenty-two supporting modules, records the source
hashes and reused local artifact hashes, and explicitly reports that a full
dependency rebuild was not performed. Both modes check twenty-five exact types and
all 148 declaration roots, permitting only `propext`, `Classical.choice`,
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

### Biased-law transfer checkpoint, 1 November 2026

The cached-dependency audit passed in
`.runtime/entropy-tail-lower-components/20261101T133250231356Z/`: all fourteen
supporting modules were rebuilt, all thirteen exact types checked, and all
86 declaration roots had only the permitted axioms. The closure contains
388 local modules, with 374 existing dependencies reused and hashed. The
nine audit regression tests, frozen-source check, project-wide proof-escape
scan, documentation file links, and whitespace check passed.

This checkpoint verifies actual stopped-transcript transfer and the stated
event/work consequences. The full information gate and final statistical
lower bound remain unproved. The canonical completeness command still
rejects `entropy_tail_lower` and `entropy_tail_law`. The finite-average
alternative above is a proposed next step, not part of this audit's claims.

### Finite averaging and population bounds checkpoint, 1 November 2026

The cached-dependency audit passed in
`.runtime/entropy-tail-lower-components/20261101T140257871598Z/`: all twenty
supporting modules were rebuilt, all twenty-two exact types checked, and
all 128 declaration roots had only the permitted axioms. The closure contains
394 local modules, with 374 dependencies reused and hashed. This is not a
full dependency rebuild. The nine audit regression tests, frozen-source
check, project-wide proof-escape scan, documentation file links, and
whitespace check passed.

This checkpoint adds actual finite averaging, arbitrary-law population
moment/work bounds, the observable early-output decomposition, and the
signwise prefix likelihood difference. The integrated early-mean estimate,
activation positivity, gated good-gap argument, and final lower bound are
outside this checkpoint's verified scope.

### Early means and gated good gaps checkpoint, 1 November 2026

The cached-dependency audit passed in
`.runtime/entropy-tail-lower-components/20261101T141608049296Z/`: all twenty-two
supporting modules were rebuilt, all twenty-five exact types checked, and
all 148 declaration roots had only the permitted axioms. The closure contains
396 local modules, with 374 dependencies reused and hashed. This is not a
full dependency rebuild. The nine audit regression tests, frozen-source
check, project-wide proof-escape scan, documentation file links, and
whitespace check passed.

This checkpoint proves the integrated early-mean estimate, positive fair
activation under the stated small-work condition, and actual gated good
gaps with exceptional mass at most `64 mZ + 4 rho`. Absorption of the rarity
term, saturation, and the final lower bound remain outside this checkpoint.
