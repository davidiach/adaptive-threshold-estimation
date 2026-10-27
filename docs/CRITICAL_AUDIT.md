# Critical quadratic theorem: follow-up audit

## Scope and source identity

This audit starts from the four-file proof bundle at published commit
`b3f88e6bc02b3d59ec9fe99529688e2bd911e1db`. Its identities are recorded in
[the existing checkpoint](../research/2026-10-27-nonlinear-critical/CHECKPOINT.md).
The audit is an additional AI source review, not human specialist review or a
new certificate for the full theorem. Existing positive reviews are evidence
to examine, not premises in the proof.

The proposed result concerns the fixed law `mu(dd)=32d dd` on `(0,1/4]`,
every measurable `0<=q<=1` with `integral q dmu<=rho`, and arbitrary observable
fresh-coin algorithms with a uniform expected-flip budget. Set
`L=1+log(1/rho)` and `H=1+log L`. The claimed RMS order is
`min(rho,sqrt(rho L H/B))`. The lower argument uses the subclass `q<=1/2`;
the upper claim must still cover the full class.

## Current formal boundary

The complete critical single-coin base-cost theorem (BC1) is proved in
[BaseCost.lean](../lean/ThresholdHC/CriticalEntropy/BaseCost.lean): one universal
positive constant gives `V E_0 T >= c rho L(1+log L)` for every
`0<rho<=1/4`, under the actual population variance, bias and finite-work
guarantees. The raw-moment version is also proved. The statistical common
hard pair, interacting-population transfer and critical upper bound remain
paper arguments. The dependency details below explain this boundary.

The finite-gap sign-entropy theorem (BC2) is now proved in
[FiniteGap.lean](../lean/ThresholdHC/CriticalEntropy/FiniteGap.lean), against the
exact `FiniteGapSignEntropyStatement` in
[Specification.lean](../lean/ThresholdHC/CriticalEntropy/Specification.lean):

$$\sum_{j=1}^K d_j^2\mathbb E_{-d_j}T\ge K\log K/512\qquad(\log K\ge32).$$

Its assumptions are `0<d_j<=1/128`, adjacent ratios `d_j/d_(j+1)>=2`,
error at most `1/10` under each sign at each gap, and finite expected work
under both signs. The same test and independent seed law apply to all gaps.
[SignTest.lean](../lean/ThresholdHC/CriticalEntropy/SignTest.lean) makes work an
extended natural stopping time and requires each terminal decision by time
`n` to be measurable from the seed and the first `n` flips. The experiment is
the product of the seed law and the constructed infinite iid Bernoulli law.
Infinite costs are retained; conversion to a real expectation occurs under
the explicit finiteness hypotheses. Termination under the fair coin is not
assumed, and nonterminating fair paths belong to none of the finite windows.

The proof derives early-decision and Markov bounds, constructs finite-prefix
windows, transfers their mass to the fair law, and counts their overlap before
applying entropy packing. It uses `ceil(4 E_-T)+1` for the upper window endpoint
to handle zero expected work uniformly; the gap bound leaves the paper's BC3,
BC4 and final constants unchanged. The abstract compact-convex common-point
component is also proved, but its statistical instantiation remains open.

The stopped-suffix foundation is now proved in
[StoppedTape.lean](../lean/ThresholdHC/CriticalEntropy/StoppedTape.lean).
For an observable procedure with an arbitrary measurable output and finite
expected work under a fixed Bernoulli parameter, the actual unused suffix has
that same Bernoulli law and is independent of both the output and stopping
time. The proof splits the iid tape at deterministic prefixes, then sums over
the countably many possible stopping times. Independence is a conclusion.
The procedure has no parameter argument; infinite work remains explicit in
[its model](../lean/ThresholdHC/CriticalEntropy/StoppedModel.lean).

The sequential realization is constructed in
[SequentialModel.lean](../lean/ThresholdHC/CriticalEntropy/SequentialModel.lean):
it runs two procedures on successive blocks of one tape, with separate seed
coordinates. Its finite stopping decisions and outputs are proved observable
pointwise. [RestartPair.lean](../lean/ThresholdHC/CriticalEntropy/RestartPair.lean)
then proves the product output law and exact addition of expected work under
independent seed laws. Only the first procedure needs finite expected work;
the second may have infinite expectation, which the identity retains. The
stronger joint identity includes both stopping times alongside both outputs.

The finite iteration is constructed in
[RepeatedModel.lean](../lean/ThresholdHC/CriticalEntropy/RepeatedModel.lean).
It takes a fixed-length vector of independent seeds and runs the same procedure
successively on one tape. [RepeatedRestart.lean](../lean/ThresholdHC/CriticalEntropy/RepeatedRestart.lean)
proves its full iid joint output law and expected work exactly `n E T`, including
the zero-repetition case. The number of repetitions is fixed before observing
flips; no latent gap or sign is passed to the procedure.

The [observable sign-test model](../lean/ThresholdHC/CriticalEntropy/RepeatedSignModel.lean)
thresholds the repeated real outputs. [SignReduction.lean](../lean/ThresholdHC/CriticalEntropy/SignReduction.lean)
proves exact work `n E T` and error at most `M/(n a^2)` when the appropriate
mean is separated from the threshold by `a>0` and its raw second moment is at
most `M`. These are bounds on the actual stopped procedure's output law,
derived from the iid realization and finite-product moment identities.

Consequently, [EstimationEntropy.lean](../lean/ThresholdHC/CriticalEntropy/EstimationEntropy.lean)
proves `sum_j d_j^2 E_-j T >= K log(K)/(512 n)` directly for a real-output
procedure under the same geometric gap conditions. Its conditional means are
at most `1/8` under minus and at least `5/8` under plus, its raw second moments
are at most `M`, and `n>=160 M` is positive. Square integrability and finite
expected work under both signs are explicit hypotheses. The proof constructs
one sign test at threshold `3/8`; no test, independence, information, or
error bound is assumed. The paper's choice `n=ceil(512(1+r))` is also checked
to satisfy `160(1/64+2r)<=n<=1282r` for `r>=2/3`.

The population step is constructed in
[PopulationModel.lean](../lean/ThresholdHC/CriticalEntropy/PopulationModel.lean):
sample the latent gap, an independent uniform sign selector, an arbitrary
independent seed, and an infinite uniform tape. Thresholding each tape coordinate
at the latent Bernoulli parameter generates the observations. The procedure
receives only its seed and those observations. [UniformCoin.lean](../lean/ThresholdHC/CriticalEntropy/UniformCoin.lean)
proves that this construction has the original infinite Bernoulli tape law and
that conditional means, extended second moments, and extended work are measurable
in the parameter, including its endpoints.

[PopulationMixture.lean](../lean/ThresholdHC/CriticalEntropy/PopulationMixture.lean)
then proves the weighted conditional moment and work formulas for every measurable
sign prior, retaining infinite values. The signed mean formula requires finite
population second moment, from which integrability is proved. Finite second moment
and work at the all-negative law and one positive constant prior imply a common
full-measure set of gaps with square-integrable output and finite work under both
signs. Both conditional means are integrable over the gap law. Moment and work
are also finite at every measurable prior; this statement does not provide the
uniform numerical bound needed for good-gap selection.

The variance bridge in
[PopulationVariance.lean](../lean/ThresholdHC/CriticalEntropy/PopulationVariance.lean)
proves the BC5 floor from bias at the null and constant-prior populations and
then the BC6 raw-moment bound. Finiteness is required of extended variance;
square integrability and raw-moment finiteness are derived. This avoids using
Mathlib's totalized real variance to hide infinite second moments.

The quantitative good-set construction (BC8) is proved in
[GoodGaps.lean](../lean/ThresholdHC/CriticalEntropy/GoodGaps.lean). Its
[model](../lean/ThresholdHC/CriticalEntropy/GoodGapModel.lean) quantifies the
uniform guarantees over the actual capped global class `q<=1/2`,
`integral q<=rho`. [GapSelection.lean](../lean/ThresholdHC/CriticalEntropy/GapSelection.lean)
uses continuity of the distribution function and the intermediate value theorem
to trim measurable subsets of an atomless bounded real law to mass `2 rho`.
[HalfPrior.lean](../lean/ThresholdHC/CriticalEntropy/HalfPrior.lean) constructs
the resulting admissible `q=1_E/2` populations and proves their exact mean and
moment changes. These facts bound the three exceptional sets and produce
`mu(G^c)<=70m`. All conditional mean, second-moment, and work bounds on `G`
are conclusions.

The quadratic gap law is now constructed and normalized in
[CriticalLaw.lean](../lean/ThresholdHC/CriticalEntropy/CriticalLaw.lean). It is
an atomless probability measure of density `32d` on `(0,1/4]`; its interval
masses and the actual Bernoulli parameter `1/2 +/- d` on that support are
proved. The separated annuli `I_j=(u_j/2,u_j]`, `u_j=1/(4*4^j)`, have
exact mass `3/(4*16^j)`.
[CriticalAnnuli.lean](../lean/ThresholdHC/CriticalEntropy/CriticalAnnuli.lean)
selects a good point in each annulus whose mass is at least `140m`.
The proof handles zero annulus work without a positive-work assumption.
Pairwise disjointness and annulus averaging give `sum_j d_j^2 w(d_j)<=W0/3`.

[CriticalScale.lean](../lean/ThresholdHC/CriticalEntropy/CriticalScale.lean)
then proves `rho K log(K)<=(656384/3)m W0`, starting from the actual uniform
population guarantees of the same observable procedure and seed law.
The conditional moments, finite work, good gaps, iid restarts and sign test
are derived. The remaining explicit hypotheses are `m>=2rho/3`,
`log(K)>=32`, and mass at least `140m` for annuli indexed `3,...,K+2`.
This intermediate theorem retains its finite-scale hypotheses. They are now
discharged in the full single-coin base-cost theorem below.

[ActivationModel.lean](../lean/ThresholdHC/CriticalEntropy/ActivationModel.lean)
defines activation solely from the seed and constructs the observable output
`Z=pY+c`. [Activation.lean](../lean/ThresholdHC/CriticalEntropy/Activation.lean)
proves the zero-flip output is population independent, so the null and
constant-prior bias bounds force `p>0`. Conditioning changes only the seed
law. It preserves every population mean, has work `E_q T/p`, and second
moment at most `p E_q Y^2+(E_q Y)^2`. The moment proof expands the square
and uses `2c E_q Y-c^2<=(E_q Y)^2`, avoiding division by `1-p` and covering
`p=1` in the same argument. All integral identities use proved finiteness.

[ActivationCost.lean](../lean/ThresholdHC/CriticalEntropy/ActivationCost.lean)
then proves BC7 for `P=M E_0 T`: the active moment bound `m` satisfies
`m>=2rho/3`, `m<=4P`, `m E_0 T_Z<=4P`, and `P>=rho/6`. Neither positive
activation nor any transformed-procedure guarantee is assumed.
[ScaleAsymptotics.lean](../lean/ThresholdHC/CriticalEntropy/ScaleAsymptotics.lean)
chooses `K=floor(log(1/rho)/(8 log 16))` below a universal rarity threshold,
proves the annulus-mass and logarithmic inequalities, and covers the remaining
interval using `P>=rho/6`. This provides one positive universal constant.

[BaseCost.lean](../lean/ThresholdHC/CriticalEntropy/BaseCost.lean) composes the
actual statistical and analytic chain to prove both the raw-moment and
extended-variance versions of `V E_0 T>=c rho L(1+log L)` for every rarity.
The same seed law and observable procedure apply to all priors. Uniform bias
and extended-variance bounds, plus finite work under each prior in the capped
global class, are the only statistical guarantees assumed. This includes the
paper's stronger uniform finite-work hypothesis. It proves BC1, but does not
prove the common hard pair, interacting-population transfer, or critical upper
construction.

The [tenth audit record](../results/critical_components_010.json) checks twenty
exact targets and all 290 public declarations using only the permitted standard
axioms. The [ninth record](../results/critical_components_009.json) preserves
the finite-scale checkpoint. The [eighth record](../results/critical_components_008.json) preserves
the fifteen-target good-gap checkpoint. The [seventh record](../results/critical_components_007.json) preserves
the twelve-target population-moment checkpoint. The [sixth record](../results/critical_components_006.json) preserves the
ten-target estimator-entropy checkpoint. The [fifth record](../results/critical_components_005.json) preserves
the finite-repetition checkpoint; the [fourth record](../results/critical_components_004.json)
preserves the six-target stopped-suffix checkpoint, and the
[third record](../results/critical_components_003.json) the finite-gap checkpoint. These targets were
introduced with their proofs, not retrospectively described as a pre-proof
freeze. The single-coin continuum null-cost product is now verified. The
full critical minimax law is **not**: common-pair instantiation, population
transfer, and the critical upper construction remain below.

## Initial dependency audit

The following records checks of actual arguments, with their remaining proof
obligations. No blocking mathematical error has been established in this first
pass. That is weaker evidence than an independently reconstructed or formal
proof.

| Dependency | Check performed | Remaining verification |
|---|---|---|
| Finite-gap sign entropy, BC2 | Early decisions use deterministic-prefix KL, not optional stopping under the fair coin. The events share one terminal time, making the scale-window overlap argument applicable. The fair law need not terminate. | Complete for the stated statistical model; see the current formal boundary above. |
| Conditional moments and response | The populations `q=0` and `q=rho` give finite conditional second moments and work outside a common null set. The response bound comes from expectations before pointwise means are used. | Complete for the stated population model; see the current formal boundary above. |
| First-observation normalization | The activation event is seed-only. Under its conditional seed law, `Z=pY+c` preserves means and changes null work to `W0/p`; the zero-activation case contradicts the bias requirement. | Complete for the actual seed-conditioned procedure; see the current formal boundary above. |
| Good-gap selection | The proof uses populations `(1/2)1_E` with `mu(E)=2rho`, respecting the lower subclass's pointwise cap. The excluded mass is at most `70m`. | Subset selection, good gaps, annulus averaging and the rarity-dependent scale count are proved. |
| Sign-test restarts | The actual unused-suffix law, observable fixed-count repetition, sign-test errors and exact `n E T` work are Lean-checked. The finite-gap estimator entropy theorem constructs this reduction from conditional moments. | The finite-scale quadratic product theorem now derives these assumptions from uniform population guarantees. |
| Finite observation reduction | At cap `m`, each seed/word cell has the integrated likelihood determined by `(T,heads)`. The multiplier cancels from conditional seed/word laws. | Formalize sufficiency, including arbitrary measurable seeds. |
| Convex RMS comparison | Finite categorical probabilities are affine and positive; log moments are concave in the population and convex in the score/scale. Tail integration is used to obtain RMS, rather than substituting a confidence bound. | Kernel treatment of the minimax interchange and tail integrals remains open. |
| One pair for all policies | The separated-pair set is compact convex in the weak-star topology. Squared Hellinger is continuous convex. A revealed finite policy mixture has exactly averaged Hellinger and null work. Finite-simplex minimax supplies the finite intersection property. | Formalize the compactness and minimax steps; a policy-dependent hard pair alone would not suffice. |
| Interacting population transfer | Leaf likelihoods factor by genuine coin even with interleaving. The midpoint hybrid simulations use independent auxiliary tapes. Since midpoint `q<=1/2`, its one-coin law dominates half the null law, giving the required cost direction. | Formalize the finite-prefix decomposition and simulation. Existing finite examples do not prove the general statement. |
| Unbounded stopping | The same pair applies at every cap. Uniform work gives termination separately under both endpoints; terminal events are approximated by stopped-prefix events. | Prove the limit without assuming termination transfers from one endpoint to the other. |
| Upper construction | Wrong-sign likelihoods are supermartingales; forced-majority error is bounded on the complete iid tape. Positive work is integrated under a global mass constraint, not a pointwise bound on `q`. The random telescope and Poisson replication use separately finite moments. | Full probability and algorithm realization remain paper arguments. |

## Specific constants and edge cases checked

* In BC5, `(1-rho)(31/32)^2 >= 2/3` on `0<rho<=1/4`; this also justifies
  replacing the raw second moment by at most `3V`/`2` in BC6.
* In BC7, the active procedure has `W0Z>=1`, `pM>=rho/6`, and
  `m<=4pM`. These inequalities retain null-population work throughout.
* In BC8, `4rho<=6m` makes `64m+4rho<=70m`. Every retained annulus has
  mass at least `140m`, so it cannot be swallowed by the excluded set.
* For `m/rho>=2/3`, the restart count satisfies
  `ceil(512(1+m/rho))<=1282m/rho`.
* The annulus comparison uses `d_j^2/mu(I_j)<=4a^2/3`; the averaging
  factor four gives the displayed `16a^2/3` work charge.
* Zero-work capped policies have population-independent transcripts. The
  hard-pair proof handles this case before any division by work.
* The statistical modulus is not identified with the variational optimizer's
  population profile. The claimed hard pair is existential.

## Primary-source checks

The follow-up consulted [Sion's original paper](https://msp.org/pjm/1958/8-1/pjm-v8-n1-p14-s.pdf)
and [Chen--Li--Qiao](https://arxiv.org/html/1608.06031v2). Sion's convexity,
semicontinuity and compactness requirements must be discharged at each use.
The latter provides prior-art context for scale entropy, and its Remark D.4
explicitly extends the mechanism to interior Bernoulli laws. This agrees with
the earlier source audit. The present arbitrary separated gaps, error level,
and displayed constants still require the written adaptation; the Bernoulli
extension itself is not a new contribution. This is a targeted dependency check, not a search
establishing novelty or publication priority.

## Formalization boundary and first checkpoint

At the first checkpoint, two exact component targets and all nine public declarations passed the local
Lean audit using only `propext`, `Classical.choice`, and `Quot.sound`:

* [Packing.lean](../lean/ThresholdHC/CriticalEntropy/Packing.lean) proves the
  probability-space event-packing inequality and the implication from BC4 to
  `c >= log(K)/512` for `log(K)>=32`. BC4 is an explicit hypothesis of the
  latter theorem. Constructing the sign-test events is still required.
* [CommonPoint.lean](../lean/ThresholdHC/CriticalEntropy/CommonPoint.lean) proves
  the abstract quantifier interchange: on a nonempty compact convex set, a
  family of continuous convex constraints admits one point satisfying all of
  them if every finite convex mixture has some feasible point. The proof uses
  a finite-simplex saddle point and compactness. Realizing the population-pair
  set, proving its weak-star compactness, and establishing the statistical
  mixture bound remain separate obligations.

[Specification.lean](../lean/ThresholdHC/CriticalEntropy/Specification.lean)
states these targets without importing their proofs; the audit checks exact
types. These specifications were introduced alongside the proofs, not frozen
beforehand. [Recorded evidence](../results/critical_components_001.json) contains
the source identities, commands, exit codes and transitive axioms. Reproduce it
with `python tools/verify_critical_components.py`; fresh output is written under
the ignored `.runtime/critical-components/` directory.

That checkpoint did not prove the finite-gap sign-testing theorem, the
base-cost theorem, or the full critical minimax law. Later checkpoints prove
the first two, as recorded in the current formal boundary above.
The full completion criteria remain in [WORKPLAN.md](WORKPLAN.md).

## Constructed Bernoulli prefix information

The second checkpoint connected probability measures to the information step.
[BernoulliPrefix.lean](../lean/ThresholdHC/CriticalEntropy/BernoulliPrefix.lean)
proves that an arbitrary common independent seed and `n` iid Bernoulli flips
have KL exactly `n * klB(p,q)`. The proof constructs the finite likelihood
density, proves the product identity, identifies finite prefixes of the
infinite iid law, and applies data processing to any measurable statistic of
the seed and prefix. Its upper bound is derived from the flip probabilities;
no information inequality is an assumption of the statistical target.

[EventInformation.lean](../lean/ThresholdHC/CriticalEntropy/EventInformation.lean)
proves the resulting event transfer. In particular, if an event at a finite
prefix has probability at least `1/4` under parameter `p` and
`n*(p-1/2)^2 <= 4*c+1/4`, its probability under the fair coin is at least
`exp(-64*c-8)`, matching BC3. The seed space is arbitrary, and no fair-coin
termination hypothesis occurs.

At that checkpoint, constructing the events from a general stopping rule
remained open. The current finite-gap theorem above completes that step and
its overlap argument. The continuum null-cost base theorem still needs the
restart and good-gap selection arguments. Four exact component targets and
25 declarations were checked in [the second record](../results/critical_components_002.json), which preserves
their source identities and axiom reports. The original record remains a
record of the earlier, narrower checkpoint.
