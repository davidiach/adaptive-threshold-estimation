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
| [GateMomentFloor](../lean/ThresholdHC/EntropyTailLower/GateMomentFloor.lean) | Proves `rho/2 <= mZ` under the same small-work condition, using actual integrated mean separation and the population variance inequality. This absorbs the additive rarity term and gives excluded mass at most `72 mZ`. |
| [GatedAnnular](../lean/ThresholdHC/EntropyTailLower/GatedAnnular.lean) | For arbitrary probability laws on `EntropyGap` supported below `a <= 1/4`, proves `min(s/a^2, rho Gamma) <= 2^30 exp(48) m W0`, where the separated annuli each have mass at least `s <= 1`. No small-work premise remains. The original capped population guarantee is still required. |
| [CertificateCentering](../lean/ThresholdHC/EntropyTailLower/CertificateCentering.lean) | Centers a feasible finite stopping certificate at its null mean while preserving work, doubling its bias allowance, and quadrupling its variance allowance. Zero intensity forces bias at least `rho/2`. |
| [FlowOneCoin](../lean/ThresholdHC/EntropyTailLower/FlowOneCoin.lean) | Realizes a cone flow as an actual capped one-coin procedure with an independent finite decision-table seed. Its population mean is the flow output count mean, its second moment is at most intensity times the moment count mean, and its work is the continuation count mean divided by positive intensity. |
| [CertificateOneCoin](../lean/ThresholdHC/EntropyTailLower/CertificateOneCoin.lean) | Proves the required selection lower bound directly when certificate bias is at least `rho/128`. For smaller bias, constructs the actual capped one-coin guarantee and proves `m W0 <= 4 B variance`. Component localization and packing remain separate. |
| [PopulationPullback](../lean/ThresholdHC/EntropyTailLower/PopulationPullback.lean) | Proves exact population integral identities and capped-prior extension under measurable parameter embeddings. Pulls back the actual guarantee from the original gap space to `EntropyGap`, preserving both original coin parameters. |
| [CertificateAnnular](../lean/ThresholdHC/EntropyTailLower/CertificateAnnular.lean) | For a feasible small-bias certificate on the included small-gap law, proves `min(s/a^2, rho Gamma) <= 2^32 exp(48) B variance`. This is a single-component obstruction with the same explicit support and separated-band hypotheses. It does not yet combine components under a global rarity allocation. |
| [ComponentPriors](../lean/ThresholdHC/EntropyTailLower/ComponentPriors.lean) | Pastes disjoint component priors under one global rarity budget. Proves joint absolute bias-response error at most `2 bias`, and additive component moment and work bounds at most the original variance and work allowances. |
| [ComponentLocalization](../lean/ThresholdHC/EntropyTailLower/ComponentLocalization.lean) | Normalizes arbitrary positive-mass restrictions and constructs actual feasible component certificates using attained worst-case priors. Their mass-weighted biases total at most `2 bias`; mass-weighted variance and work stay within the original allowances. |
| [LocalizationAlgebra](../lean/ThresholdHC/EntropyTailLower/LocalizationAlgebra.lean) | Splits components by bias accuracy and combines the accurate components by finite Cauchy--Schwarz. Its budget premises are supplied by the component certificate construction. |
| [LocalizedAnnular](../lean/ThresholdHC/EntropyTailLower/LocalizedAnnular.lean) | Combines the actual component certificates with annular saturation, giving total eligible component cost at most `256 bias + sqrt(2^32 exp(48) variance)`. The single-band specialization also proves the finite rarity-allocation obstruction directly. The component families and canonical cost comparison remain explicit obligations. |
| [CanonicalBands](../lean/ThresholdHC/EntropyTailLower/CanonicalBands.lean) | Constructs normalized small-gap laws from the original canonical bands and proves their finite rarity-allocation bound for indices at least six, including zero allocations and empty bands. It also proves the scalar allocation comparison. The original experiment is unchanged. |
| [DyadicMass](../lean/ThresholdHC/EntropyTailLower/DyadicMass.lean) | Constructs a fractional upper-tail mass cut and proves the factor-two dyadic top-mass inequality for arbitrary nonnegative finite mass vectors whose entries are bounded by the mass budget. |
| [EntropyIncrement](../lean/ThresholdHC/EntropyTailLower/EntropyIncrement.lean) | Proves a square-root entropy increment bound with coefficient two, and a binary entropy decrement bound. These deterministic estimates allow zero coordinates. |
| [FiniteSelection](../lean/ThresholdHC/EntropyTailLower/FiniteSelection.lean) | Proves existence of finite selection minimizers and derives ordinary-band mass at most `4 rho` from their optimality. This conservative constant is weaker than the paper's `rho` bound and suffices for the proposed route. It does not yet bound the complete selection objective. |
| [FiniteAllocation](../lean/ThresholdHC/EntropyTailLower/FiniteAllocation.lean) | Proves restriction and ordinary/ignored cost comparisons for finite rarity allocations, and connects the allocation interface to the checked canonical small-gap certificate bound. |
| [CertificateLabel](../lean/ThresholdHC/EntropyTailLower/CertificateLabel.lean) | Derives `rho <= 16 B variance` for small-bias certificates without a gap-support restriction. The resulting capped label cost is at most `128 bias + 4 sqrt(variance)`. |
| [LargeGapEntropy](../lean/ThresholdHC/EntropyTailLower/LargeGapEntropy.lean) | Bounds the canonical entropy in the first six bands by 16384 and derives their capped entropy cost at most `16384 bias + 512 sqrt(variance)` for the original probability law. |
| [LabelAllocation](../lean/ThresholdHC/EntropyTailLower/LabelAllocation.lean) | Combines support-independent label bounds through the actual normalized certificates and joint budgets. Allows atoms, empty bands, and zero allocations. |
| [GlobalCosts](../lean/ThresholdHC/EntropyTailLower/GlobalCosts.lean) | Combines label and annular bounds to cover every canonical band. For `R = 256 bias + sqrt(2^32 exp(48) variance)`, proves finite allocation cost at most `65 R`, ordinary cost of any optimal finite selection at most `2080 R`, and rarity-capped ignored mass at most `260 R`. Proves the exact ordinary/ignored penalty decomposition. |
| [RetainedGap](../lean/ThresholdHC/EntropyTailLower/RetainedGap.lean) | Derives the exact entropy decrement when erasing a retained band and its logarithmic lower bound. Optimality gives `sqrt(rho) (1 + log(A/a_j)) <= 2 b_j sqrt(F)` for each positive retained band. |
| [EntropyPacking](../lean/ThresholdHC/EntropyTailLower/EntropyPacking.lean) | Proves finite entropy decomposition and geometric reference estimates, comparable-cost bounds, and factor-64 entropy preservation when at least half the comparable bands remain. The integer trimming size and gap amplification are checked under explicit separation premises; the actual tier/parity construction and saturation allocation remain. |

The supporting weighted-sign target and its dependency hashes were recorded
before accepting its proof in
[the new specification lock](../tools/entropy_tail_lower_specification_freeze.json).
The coefficient is conservative and is not the paper's sharper coefficient.
No existing specification, manuscript, or published evidence is changed.

## Remaining mathematical work

1. Construct the retained-band entropy packing: split positive cost weights
   into comparable groups and parity classes, instantiate the checked trimming
   bounds, and allocate rarity while preserving the actual minimum-band-mass
   saturation condition. The logarithmic retained-gap condition and the
   deterministic entropy/trimming helpers are now checked. The localized
   annular theorem still requires the actual component choices and cost
   comparisons. Ordinary, capped ignored, and first-six-band costs are bounded.

2. Prove the canonical finite-prefix comparison and limit for arbitrary laws,
   maintaining the original selection functional and global rarity budget.
   The lower-bound route needs an upper comparison of the original selection
   functional with twice the finite-prefix optimum plus the omitted tail mass,
   followed by the vanishing-tail limit at each fixed law. The full continuous
   variational modulus is not a claimed theorem.
3. Prove `CertificateLowerStatement`, apply the checked equivalence, and
   register `entropy_tail_lower` against the original frozen specification.
   Then assemble the two-sided entropy-tail and closed-quantile laws and run
   their full exact-type audits.

The certificate route can reuse the existing formal treatment of arbitrary
adaptive population algorithms. It does not make the remaining steps automatic.

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
whose excluded mass is at most `64 mZ + 4 rho`. The moment floor
`rho/2 <= mZ` improves this to `72 mZ`. Annular averaging then gives the
entropy bound when all annular masses exceed
`288 exp(12) (1 + exp(12)) a^2 m W0`. Splitting off the complementary
small-mass and large-work cases proves the saturated minimum bound in the
table. Its coefficient is conservative; it is not the paper's coefficient.
The whole-law certificate connection and additive finite-certificate
localization below are proved; the final selection comparison remains.
Rejection-loop renewal has not been formalized and is not used by this
fixed-repeat construction.

### Finite-certificate connection

For a feasible certificate with bias at most `rho/128`, the root intensity
`i` is positive. Centering its flow at the null mean preserves the work
bound. The independent finite decision-table mixture gives an actual
one-coin procedure with the original capped population bias guarantee,
moment allowance `m = 4 i variance`, and work at most `B/i` under every
capped prior. Thus `m W0 <= 4 B variance`. All flips of the selected table
are charged, and the procedure observes only its independent seed and tape.

If the certificate bias is at least `rho/128`, the outer rarity cap of the
original selection functional gives the desired certificate inequality
with coefficient `1/128` directly. The remaining lower-bound work concerns
small-bias certificates and the deterministic comparison with selection.

Measurable embedding now transfers the actual guarantee to a small-gap law
without changing its coin parameters. Combining it with the saturated
annular theorem gives
`min(s/a^2, rho Gamma) <= 2^32 exp(48) B variance` for each feasible
small-bias certificate on such a law. The construction below supplies normalized
component certificates and combines their annular obstructions under one
global budget.

### Additive finite-certificate localization

Let `S_i` be disjoint measurable sets of positive mass `tau_i`, and let
nonnegative conditional rarity allowances satisfy `sum tau_i r_i <= rho`.
The checked construction gives feasible certificates on each normalized
restriction. Each keeps the original flow, with an independently centered
offset and attained worst-case bias, moment, and work allowances. Their
joint bounds are

```text
sum tau_i bias_i <= 2 bias,
sum tau_i variance_i <= variance,
sum tau_i work_i <= B.
```

These bounds follow from actual admissible pasted priors, including for
laws with atoms. At positive budget and cap, for identified small-gap
component laws with `0 < r_i <= 1/4` satisfying the annular support,
separation, and mass conditions, take nonnegative costs
`u_i <= tau_i r_i` with
`u_i^2 B <= tau_i^2 min(s_i/a_i^2, r_i Gamma_i)`. The resulting checked bound is

```text
sum u_i <= 256 bias + sqrt(2^32 exp(48) variance).
```

For a component contained in one annulus `(b_i/2,b_i]`, the checked
specialization supplies the eligible cost directly as
`tau_i min(r_i, sqrt(r_i/(B b_i^2)))`. Thus finite single-band rarity
allocations have the same additive bound.

The statistical certificates and additive budgets are derived in this
theorem. The deterministic selection proof must still provide the component
families, their rarity allocation, their normalized small-gap laws, and the
displayed cost comparisons. No bound for the full original selection
functional is inferred before those steps and the remaining variational
and finite-prefix arguments are proved.

### Ordinary, ignored, and larger-gap costs

Write `R = 256 bias + sqrt(2^32 exp(48) variance)` for a feasible positive-cap
certificate at positive budget. The support-independent label bound and
its component localization extend the finite allocation inequality to all
canonical bands, with coefficient 65. Conditional rarities lie in `[0,1/4]`
and their mass-weighted total stays within the original rarity budget.

For any minimizer of the finite canonical score at `h = 1/sqrt(B)`, the
checked ordinary cost is at most `2080 R`. The ignored mass, capped by
`rho`, is at most `260 R` for any finite selection. The bandwise penalty
decomposes exactly into ordinary cost plus ignored mass; the uncapped
ignored mass is not claimed bounded by `260 R`.

The first six bands have total canonical entropy at most 16384, including
after retaining any subset. For `0 < rho <= 1`, their capped entropy cost
is at most `16384 bias + 512 sqrt(variance)`. This uses actual finite
certificates on the original gap law and requires no small-gap assumption.
The remaining retained small-gap entropy still needs the packing argument.

### Retained-gap optimality and deterministic trimming

For a minimizer of the finite score, let `F` be its retained entropy and `A`
its retained cost mass. Every positive retained band satisfies
`sqrt(rho) (1 + log(A/a_j)) <= 2 b_j sqrt(F)`. The proof uses the exact change
in entropy on erasing one coordinate, a binary-entropy lower bound, and
optimality against assigning that coordinate to the complementary penalty.
It does not assume differentiability at a zero coordinate.

Finite entropy decomposes exactly into within-group entropy and entropy of
the group masses. The geometric reference estimate and its finite weighted
sum are checked. For costs in a factor-four interval, keeping at least half
the coordinates preserves entropy within a factor of 64. For every nonempty
group, removing `ceil(log_4 n)` indices leaves at least half. Removing those
indices from the smallest-gap end of an explicitly separated ordered family
gains a factor `n` in its minimum retained gap.

These are deterministic ingredients. The construction of the actual
cost-tier/parity groups, their canonical separation, the saturated component
allocation, and the resulting retained-entropy lower bound remain unproved.

## Verification

Run the new audit from the repository root:

```sh
python tools/verify_entropy_tail_lower_components.py
python -m unittest discover -s tools -p 'test_entropy_tail_lower_components.py' -v
```

The default rebuilds the entire local dependency closure. With
`--cached-dependencies`, it rebuilds the forty-four supporting modules, records the source
hashes and reused local artifact hashes, and explicitly reports that a full
dependency rebuild was not performed. Both modes check seventy-six exact types and
all 301 declaration roots, permitting only `propext`, `Classical.choice`,
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

### Gated annular saturation checkpoint, 1 November 2026

The cached-dependency audit passed in
`.runtime/entropy-tail-lower-components/20261101T143010989137Z/`: all twenty-four
supporting modules were rebuilt, all twenty-eight exact types checked, and
all 155 declaration roots had only the permitted axioms. The closure contains
398 local modules, with 374 dependencies reused and hashed. This is not a
full dependency rebuild. The nine audit regression tests, frozen-source
check, project-wide proof-escape scan, documentation file links, and
whitespace check passed.

This checkpoint proves the gated moment floor, the `72 mZ` exceptional-mass
bound, and the saturated annular lower bound with coefficient `2^30 exp(48)`.
The certificate connection, component localization, selection/packing, and
canonical finite-prefix limit remain outside this checkpoint. The canonical
lower and two-sided laws remain unproved.

### Actual one-coin certificate checkpoint, 1 November 2026

The cached-dependency audit passed in
`.runtime/entropy-tail-lower-components/20261101T144512840210Z/`: all twenty-seven
supporting modules were rebuilt, all thirty-seven exact types checked, and
all 181 declaration roots had only the permitted axioms. The closure contains
405 local modules, with 378 dependencies reused and hashed. The reused local
dependency sources match the `entropy-tail-integrated` cache checkout byte
for byte. This is not a full dependency rebuild. The nine audit regression
tests, frozen-source check, project-wide proof-escape scan, documentation
file links, and whitespace check passed.

This checkpoint proves certificate centering, actual finite decision-table
realization, the small-bias capped guarantee with `m W0 <= 4 B variance`, and
the large-bias selection bound with coefficient `1/128`. Component
localization, selection/packing, and the canonical finite-prefix limit remain
open. The canonical lower and two-sided laws remain unproved.

### Parameter transfer and certificate annular checkpoint, 1 November 2026

The cached-dependency audit passed in
`.runtime/entropy-tail-lower-components/20261101T150156246216Z/`: all twenty-nine
supporting modules were rebuilt, all forty-one exact types checked, and all
189 declaration roots had only the permitted axioms. The closure contains
407 local modules, with 378 dependencies reused and hashed. This is not a
full dependency rebuild. The nine audit regression tests, frozen-source
check, project-wide proof-escape scan, documentation file links, and
whitespace check passed.

This checkpoint preserves the actual capped guarantee under measurable
parameter embedding and proves the single-component annular certificate
obstruction with coefficient `2^32 exp(48)` times `B variance`. Additive
component localization, selection/packing, and the canonical finite-prefix
limit remain outside this checkpoint. The canonical completeness check
still rejects `entropy_tail_lower` and `entropy_tail_law`.


### Additive localization and finite-band allocation checkpoint, 1 November 2026

The cached-dependency audit passed in
`.runtime/entropy-tail-lower-components/20261101T152527805783Z/`: all thirty-three
supporting modules were rebuilt, all forty-nine exact types checked, and all
216 declaration roots had only the permitted axioms. The closure contains
417 local modules, with 384 dependencies reused and hashed. The reused local
dependency sources match the `entropy-tail-integrated` cache checkout byte
for byte. This is not a full dependency rebuild. The nine audit regression
tests, frozen-source check, project-wide proof-escape scan, documentation
file links, and whitespace check passed.

This was a fresh sequential retry after the earlier audit at
`20261101T151839654871Z` stopped on a cached Mathlib artifact read error.
That earlier failed record remains unchanged; it is not counted as a pass.

The checkpoint derives actual normalized component certificates with joint
bias, variance, and work budgets, then combines their saturated annular
obstructions. It also derives finite single-band rarity-allocation costs.
The ordinary/ignored cost comparison, deterministic packing, canonical
finite-prefix limit, and final lower/law assembly remain open. The canonical
completeness check still rejects `entropy_tail_lower` and `entropy_tail_law`.


### Canonical bands and finite selection checkpoint, 1 November 2026

The cached-dependency audit passed in
`.runtime/entropy-tail-lower-components/20261101T154903206923Z/`: all thirty-seven
supporting modules were rebuilt, all fifty-seven exact types checked, and
all 254 declaration roots had only the permitted axioms. The closure contains
421 local modules, with 384 dependencies reused and hashed. The reused local
dependency sources match the `entropy-tail-integrated` cache checkout byte
for byte. This is not a full dependency rebuild. The nine audit regression
tests, frozen-source check, proof-escape scan of all 707 Lean sources,
documentation file links, and whitespace check passed.

This checkpoint constructs the canonical small-gap component laws and
derives their finite allocation bound, including zero masses and allocations.
It proves fractional dyadic top-mass selection, the square-root entropy
increment estimate, existence of finite selection minimizers, and their
ordinary-band mass bound `w <= 4 rho`. The weaker constant is stated
explicitly; the sharper paper constant is not claimed.

The ordinary/ignored cost assembly, larger-gap treatment, retained entropy
packing, canonical finite-prefix comparison/limit, and final lower/law
assembly remain outside this checkpoint. The canonical completeness check
still rejects `entropy_tail_lower` and `entropy_tail_law`.


### Ordinary, ignored, and larger-gap checkpoint, 1 November 2026

The cached-dependency audit passed in
`.runtime/entropy-tail-lower-components/20261101T174616833433Z/`: all forty-two
supporting modules were rebuilt, all sixty-nine exact types checked, and
all 279 declaration roots had only the permitted axioms. The closure contains
426 local modules, with 384 dependencies reused and hashed. The reused local
dependency sources match the `entropy-tail-integrated` cache checkout byte
for byte. This is not a full dependency rebuild. All nine audit regression
tests, frozen-source verification, the proof-escape scan of 712 Lean sources,
documentation file links, and whitespace checks passed.

The support-independent certificate label floor and its additive localization
extend finite rarity allocations to all canonical bands. For
`R = 256 bias + sqrt(2^32 exp(48) variance)`, the allocation bound is `65 R`,
the ordinary cost of any optimal finite selection is at most `2080 R`, and
the rarity-capped ignored mass is at most `260 R`. The exact penalty split
contains uncapped ignored mass. The first-six-band entropy is at most 16384,
with its capped entropy cost at most `16384 bias + 512 sqrt(variance)`.

Retained-band optimality and entropy packing, the canonical finite-prefix
comparison and limit, and final lower/law assembly remain outside this
checkpoint. The canonical completeness check still rejects
`entropy_tail_lower` and `entropy_tail_law`.

All five GitHub CI jobs passed for the earlier 37-module commit
`ce410c8beda03faca7bfe483f2f8e914bcda6a1c` in run `41324755472`. That CI result
belongs to that commit; it does not certify this later checkpoint.


### Retained-gap and deterministic trimming checkpoint, 1 November 2026

The cached-dependency audit passed in
`.runtime/entropy-tail-lower-components/20261101T180647371920Z/`: all forty-four
supporting modules were rebuilt, all seventy-six exact types checked, and
all 301 declaration roots had only the permitted axioms. The closure contains
428 local modules, with 384 dependencies reused and hashed. The reused local
dependency sources match the `entropy-tail-integrated` cache checkout byte
for byte. This is not a full dependency rebuild. All nine audit regression
tests, frozen-source verification, the proof-escape scan of 714 Lean sources,
documentation file links, and whitespace checks passed.

Optimal retained positive bands satisfy the logarithmic gap condition,
proved through the exact entropy decrement and comparison with erasing one
coordinate. The checkpoint also proves finite entropy decomposition,
geometric reference and sum bounds, comparable-cost entropy estimates,
and factor-64 entropy preservation after retaining at least half a group.
The ceiling logarithm gives a valid trimming size; the minimum-gap increase
is proved when removing the smallest-gap end of an explicitly separated
ordered family.

Constructing the actual cost-tier/parity groups, instantiating their
separation, proving the saturated rarity allocation, the canonical
finite-prefix comparison and limit, and final lower/law assembly remain
outside this checkpoint. The canonical completeness check still rejects
`entropy_tail_lower` and `entropy_tail_law`.
