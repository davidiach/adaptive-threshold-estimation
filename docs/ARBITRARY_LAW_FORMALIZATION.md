# Arbitrary-law adaptation: formalization scope

The [arbitrary-law adaptation theorem](ARBITRARY_LAW_ADAPTATION.md) has a
paper proof. The new `ThresholdHC.ArbitraryLawAdaptation` namespace formalizes
components of that proof; it does not yet contain its full statistical theorem.
Python execution is outside the Lean verification claim.

## Finite entropy transport

For a nonnegative finite cost vector, write
`G(a) = A + sum negMulLog(a_i) - negMulLog(A)`, where `A = sum a_i`.
[EntropyTransport.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/EntropyTransport.lean)
proves a cross-entropy bound allowing zero reference weights off the cost
support, the normalized reference identity, a rowwise transport inequality,
and entropy decrease under arbitrary finite merging. In particular, if
`sum_k f_(i,k) <= a_i`, `b_(i,k) <= r_k f_(i,k)`, `r_k <= 1`, and a positive
reference subprobability satisfies `r_k (-log p_k) <= L`, then
`G(b) <= G(a) + L A` for nonnegative `a`, `f`, and `b` and `L >= 0`.

[BandPenalty.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/BandPenalty.lean)
specializes to `r_k = min(1, 4 (1/4)^k)` and `p_k = (1/2)^(k+1)`.
It proves `r_k (k+1) <= 2`, the finite geometric normalization, the coding
penalty bound, and `G(b) <= 3 G(a)`. The sizes of both finite index sets are
arbitrary. The pushforward theorem allows merging cells into their actual
destination bands.

Run `python tools/verify_arbitrary_law_entropy.py` to compile these modules
and audit 15 independently restated exact statements and their transitive
axioms. The audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
The proof-source guard is `python tools/verify_lean_sources.py`.

The [native audit record](../results/arbitrary-law-entropy-20261106/README.md)
identifies the exact proof checkpoint, sources, compiler and reused objects.

## Countable entropy transport

[CountableEntropy.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/CountableEntropy.lean)
defines entropy as the extended-valued supremum of the finite-prefix entropies.
Continuity of each finite-prefix entropy gives a limit theorem under
coordinatewise convergence. The module also proves entropy decrease when
cells are both discarded and merged, and convergence of square partial sums
to the sum of a summable array.

[CountableTransport.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/CountableTransport.lean)
applies those limits to nonnegative cells indexed by source band and displacement.
If every finite row sum of the old costs is at most `a_i`, the new cells obey
the geometric contraction bound, and each destination column is summable, then
the full transported entropy is at most `3 G(a)`. The destination map is
arbitrary. The total cost and entropy may be infinite; summability is required
only within each destination band.

[GammaTransport.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/GammaTransport.lean)
identifies this prefix supremum with the project's canonical Gamma functional
for every finite gap measure. It gives `Gamma(new) <= 3 Gamma(old)` from a
supplied countable band-cell decomposition. The increasing-gap coupling
construction below now supplies these premises for positive-gap measures.

Run `python tools/verify_arbitrary_law_countable.py` for 16 independently
restated exact statements and their transitive axiom reports.
The [native countable-transport record](../results/arbitrary-law-countable-20261106/README.md)
identifies the exact proof checkpoint and all 45 project dependencies.

## Increasing-gap coupling and fractional selections

[BandGeometry.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/BandGeometry.lean)
constructs the measurable canonical band index and proves that it decreases
when the gap increases. Its inverse-square inequality gives exactly
`min(1, 4 (1/4)^k)` for a move of `k` bands, including band endpoints.
[TransportCells.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/TransportCells.lean)
integrates measurable countable cells and proves their merging identity.
[CouplingEntropy.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/CouplingEntropy.lean)
constructs these cells for every finite measure on pairs of positive gaps
whose first coordinate is at most its second almost surely. The old row sums
equal the source band costs, and merged new columns equal the destination
band costs. Local summability follows from finite mass and bands bounded
away from zero. Consequently `Gamma(second marginal) <= 3 Gamma(first marginal)`
without any finite full-law inverse moment or entropy assumption.

[SelectionLift.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/SelectionLift.lean)
lifts every fractional selection of the first marginal using its
Radon--Nikodym density. The lifted measure is dominated by the coupling,
has the original selection as first marginal, and transports to a selection
dominated by the second marginal with exactly the same mass. Subtracting
the selection commutes with taking either marginal. The residual tail cost
decreases, while selected entropy increases by at most a factor of three.
[IncreasingSelection.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/IncreasingSelection.lean)
then proves the objective and capped-infimum comparison
`K(second marginal) <= sqrt(3) K(first marginal)`. The infimum ranges over all
fractional submeasures, including those with infinite entropy.

Run `python tools/verify_arbitrary_law_coupling.py` for 19 exact statements
and transitive axiom reports, and `python tools/verify_arbitrary_law_selection.py`
for 13 more. These results concern the canonical positive-gap space `(0,1/2]`
and a supplied increasing coupling. The next development constructs the
coupling from CDF domination and extends the functional to include zero.
The [native coupling and selection record](../results/arbitrary-law-coupling-20261106/README.md)
binds both audits to their proof checkpoint and complete project closure.

## CDF coupling and unresolved mass at zero

[CDFCoupling.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/CDFCoupling.lean)
constructs a generalized inverse of a right-continuous CDF on the unit
interval. Its exact threshold identity proves measurability and the
pushforward law under uniform volume. Two inverses driven by the same
uniform variable therefore give a probability coupling with the requested
marginals. CDF domination makes this coupling increasing. The construction
allows atoms, including at zero, for bounded nonnegative probability laws.
Run `python tools/verify_arbitrary_law_cdf_coupling.py` for 11 exact statements
and transitive axiom reports.

[ZeroModel.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/ZeroModel.lean)
defines the extended entropy and tail functional for laws on `[0,1/2]`,
represented as real measures. Selected
positive mass at zero has infinite entropy; the tail kernel at zero is one.
The infimum still ranges over all fractional submeasures. On every finite
positive-gap measure, the extended Gamma, objective and K agree with the
original quantities after embedding into the real line.

[ZeroCoupling.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/ZeroCoupling.lean)
proves the factor-three entropy comparison on `[0,1/2]`. If the source has
no zero atom, the increasing coupling stays within the positive-gap space
almost surely, where the earlier canonical-band theorem applies. If selected
source mass at zero is positive, its entropy is infinite. The tail kernel
is antitone, including its value at zero.
[ZeroSelection.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/ZeroSelection.lean)
transports every fractional selection, preserving mass and domination, and
proves the square-root-three objective and capped-infimum comparisons.

[CDFSelection.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/CDFSelection.lean)
joins these results: for probability laws on `[0,1/2]`,
`F_new <= F_old` implies `K(new) <= sqrt(3) K(old)`. The increasing coupling
is constructed, not assumed. No atomlessness, finite inverse moment or
finite entropy is required. Run `python tools/verify_arbitrary_law_zero.py`
for 36 exact statements and transitive axiom reports, including exact
agreement with the original positive-gap selection functional.
The [native CDF and zero-atom record](../results/arbitrary-law-zero-cdf-20261106/README.md)
identifies the proof checkpoint, audit inputs and complete project closure.

## Dominated mass

[ZeroAlgebra.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/ZeroAlgebra.lean)
proves homogeneity and monotonicity of the extended entropy, and the tail
cost's additivity, homogeneity and exact unit cost at zero.
[DominatedSelection.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/DominatedSelection.lean)
constructs a pointwise bounded Radon--Nikodym density. It restricts every
fractional selection to a dominated law, proving domination of the selected
measure and its residual, and hence monotonicity of K under measure domination.
[DominatedMass.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/DominatedMass.lean)
then proves (A5): `lambda <= c eta + e delta_0` implies
`K(lambda) <= c K(eta) + e`, for `c >= 1` and `e >= 0`.
Finite ambient measures suffice; no inverse moment or finite entropy is assumed.
The theorem retains the infimum over all fractional selections and the cap.

Run `python tools/verify_arbitrary_law_dominated.py` for 22 independently
restated exact statements and 22 transitive axiom reports.
The [native dominated-mass record](../results/arbitrary-law-dominated-20261106/README.md)
binds the proof checkpoint and complete project closure.

## Light random contraction

[ProductEntropy.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/ProductEntropy.lean)
proves finite and countable entropy bounds using a product reference code.
[LightContractionConstants.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/LightContractionConstants.lean)
checks the exponential and geometric-series budgets, and
[LightContractionGeometry.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/LightContractionGeometry.lean)
proves that each source/multiplier band pair has two possible destination bands.
[LightContractionCells.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/LightContractionCells.lean)
constructs those cells in the actual independent product measure and proves
`Gamma(law(VD/2)) <= 1024 Gamma(sigma)` for every finite selected measure,
assuming the stated multiplier support and dyadic probability bounds.
Local column summability suffices; full-law entropy may be infinite.

Run `python tools/verify_arbitrary_law_light_entropy.py` for 36 independently
restated exact statements and 36 transitive axiom reports.

[LightContractionTail.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/LightContractionTail.lean)
proves the inverse first-moment and integrated residual-tail bounds.
[LightContraction.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/LightContraction.lean)
derives the dyadic probability bounds from the exact multiplier CDF, transports
every fractional selection, identifies its residual, and proves the capped
infimum comparison with coefficient 32.
[LightMultiplier.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/LightMultiplier.lean)
constructs the multiplier by mapping a uniform variable to
`min(1/4, 1/sqrt(2 log(2/u)))`, assigning `1/4` at the null endpoint `u=0`.
It proves the exact CDF in (A3), probability normalization, and the factor-32
comparison for this constructed law. Independence is the actual product
measure. No multiplier-existence, finite-moment or finite-entropy premise is
needed in the final theorem; finite positive-gap input measures suffice.

Run `python tools/verify_arbitrary_law_light.py` for 26 additional exact
statements and transitive axiom reports. The proof uses a fixed two-cell
reference code to obtain the post-division entropy bound 1024 directly.
The paper's intermediate sharper `C_V < 256` calculation in (A4) is not
asserted as a separately formalized result.
The [native light-contraction record](../results/arbitrary-law-light-20261106/README.md)
binds both audits to the proof checkpoint and complete project closure.

## Finite CDF envelope

[CDFEnvelope.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/CDFEnvelope.lean)
constructs a measure on the real line from cumulative upper bounds. Taking
prefix minima preserves the finite grid bounds and makes the weights
nonnegative. The finite measure has total mass one when the first bound is
one, and its zero atom has exactly the remaining tail mass. Lean proves its
closed-CDF formula, including the preceding-bound value at each positive grid
atom, and CDF domination of every nonnegative probability law satisfying the
finitely many supplied grid bounds. No condition is imposed at unprobed cutoffs.

Run `python tools/verify_arbitrary_law_envelope.py` for 25 exact statements
and 24 transitive axiom reports. The hypotheses are deterministic finite grid
bounds; the pilot's probability guarantee for those bounds is proved in the
[pilot section](#capped-multi-depth-pilot).

The [native envelope record](../results/arbitrary-law-envelope-20261106/README.md)
preserves its proof checkpoint, exact audit input, axiom reports and empty
compilation log.

## Observable learning stage

[LearnedStage.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/LearnedStage.lean)
constructs an observable stage from a fixed paid pilot, a rule turning its
observed word into the finite envelope above, and a continuation selected by
that envelope. The pilot and continuation use disjoint persistent coin labels.
Lean proves that the continuation receives untouched tapes and that the output
computed from the chronological observed history equals the table construction.
The learned law is a probability measure on every observed word; CDF domination
follows on the finite grid event. Both endpoints share one policy and obey the
unconditional physical cap
`pilotCost + continuationCost`. Their joint output law is identified in the
original hidden-gap experiment, with arbitrary measurable gap-dependent signs.

Run `python tools/verify_arbitrary_law_stage.py` for 17 exact statements and
16 transitive axiom reports. This is a reusable execution construction. It
does not itself instantiate the statistical pilot or robust continuation, or
assume their desired risk bounds in place of proving them; the pilot is
installed in it in the [pilot section](#capped-multi-depth-pilot). It is a
single stage,
not yet the final all-budget confidence controller.

The [native stage audit](../results/arbitrary-law-stage-20261106/README.md)
identifies the 644-source project closure, exact statements and compiled
dependency hashes for that checkpoint.

## Sign-neutral tail test

This is the single-coin primitive of the
[tail certificate](ARBITRARY_LAW_TAIL.md#a-sign-neutral-test-with-a-gap-dependent-cost).
One persistent coin is inspected after `n_k = 4^k` flips, `k = 0,...,J`. Check
`k` resolves the coin when `|2S - n_k| > 2 h_k`, where `S` counts heads and
`h_k = ceil(sqrt(2 n_k (J-k+2)))`. The inequality is strict, so a tie continues,
and the coin is unresolved when the terminal check also fails.

[TailTest.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/TailTest.lean)
defines the test on a tape of flips. It proves that `h_k` is the least natural
number whose square reaches `2 n_k (J-k+2)`, that `h_J = 2^(J+1)` exactly, and
the pathwise work cap `1 <= T <= 4^J`. The stopping check and the unresolved
indicator depend only on the flips that were bought, and complementing every
flip leaves the whole stopping path unchanged.

[TailTestProbability.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/TailTestProbability.lean)
proves the bounds for a coin with heads probability `1/2 + d`. If
`d <= 2^-J`, the coin is unresolved with probability at least `1/2`. If
`d >= 4 * 2^-J`, it is unresolved with probability at most `exp(-4^J d^2 / 2)`.
Its expected work is at most `min(4^J, 1024 d^-2 (1 + log2+(d 2^J)))`. Each
bound uses Hoeffding's inequality at single checkpoints and a union bound. The
checks share one coin and are never treated as independent samples.

[TailTestLaw.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/TailTestLaw.lean)
proves that complementing flips exchanges the two signs of the coin law. A
bounded flip-invariant statistic of one fresh coin therefore has the same mean
under the original population tape law for every measurable gap-dependent
sign law. For every probability law `mu` of positive gaps and every sign law,
the unresolved probability `u_J` of a fresh coin satisfies
`F(2^-J)/2 <= u_J <= integral of min(1, 16 (2^-J/d)^2) dmu`, and
`u_J <= P(V D <= 2^-J)` for the constructed multiplier `V` of (A3), independent
of `D`. The expected work is at most the integral of the bounded work
envelope. No inverse-moment assumption is made.

Run `python tools/verify_arbitrary_law_tail_test.py` for 91 exact statements
and 91 transitive axiom reports, one for each declaration of the three
modules. The audit fails if a declaration is added without being registered.
The [tail-test record](../results/arbitrary-law-tail-test-20261110/README.md)
identifies the proof checkpoint and source hashes.

These are statements about one coin. Inverse sampling over fresh coins is the
subject of the next section. The test is not yet embedded as a reader in the
observable stage.

## Capped tail probe

This is one probe of the
[inverse-sampling step](ARBITRARY_LAW_TAIL.md#inverse-sampling-under-a-physical-budget),
with the coin cap of
[adaptation (A7)](ARBITRARY_LAW_ADAPTATION.md#2-learning-the-envelope-under-one-physical-cap).
Fresh coins are tested one after another with the tail test. The probe stops
when it completes an unresolved coin, when it has completed `M` coins, or when
its flip budget `b` is exhausted. After `n` completed coins it returns
`V = min(1, 8/n)`, and `V = 1` when `n = 0`.

[TailProbe.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/TailProbe.lean)
defines the probe on a stream of tapes, one tape for each fresh coin. On every
stream the charge is at most `b` and at most `M 4^J`, and at most `min(b, M)`
coins are completed. A coin that the budget interrupts is charged for the flips
bought on it and is not counted. Raising the budget never lowers the completed
count or the charge, and a coin cap of at least `b` does not change the
completed count. The completed count, the charge and the final verdict depend
only on the bought flips.

[TailProbeProbability.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/TailProbeProbability.lean)
takes independent coins whose tapes share an arbitrary probability law, and
writes `u` for the probability that one coin is unresolved. If `F <= 1` and
`F <= 2u`, then with probability at least `7/8` the certificate is at least `F`
at every flip budget and every coin cap simultaneously. The proof bounds the
event that the first `floor(4/u)` coins are all resolved, which has probability
`(1-u)^floor(4/u)`. It never treats the number of completed coins as a fixed
sample size. At a fixed budget `b >= 1` and coin cap `M >= 1`, with probability
at least `3/4` the certificate is at most `min(1, 128 max(u, W/b, 1/M))`, for
every `W` that bounds the expected work of one coin. The two failure events
are joined by a union bound and are not assumed independent.

[TailProbeLaw.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/TailProbeLaw.lean)
states both results on the coin array of the original simulation law, for
every probability law `mu` of positive gaps and every measurable gap-dependent
sign law. There `F = F(2^-J) = mu((0, 2^-J])`, `u = u_J`, and `W = W_J` is the
integral of the bounded work envelope. Without a coin cap the performance
bound is `min(1, 128 max(u_J, W_J/b))`, which is (5) of the tail certificate.
With the cap it is (A7).

Run `python tools/verify_arbitrary_law_tail_probe.py` for 69 exact statements
and 69 transitive axiom reports, one for each declaration of the three
modules. The audit fails if a declaration is added without being registered.
The [tail-probe record](../results/arbitrary-law-tail-probe-20261110/README.md)
identifies the proof checkpoint and source hashes.

These are statements about one probe at one depth. The median over independent
probes is the subject of the next section. The probe is defined on a stream of
tapes; its reader of observed flips is the subject of
[a later section](#tail-certificate-in-the-observable-experiment).

## Median tail certificate

This is the amplification step of the
[tail certificate](ARBITRARY_LAW_TAIL.md#inverse-sampling-under-a-physical-budget).
`m` probes at depth `J` run on separate streams of fresh coins, and the
certificate `U` is the median of their certificates: the entry of rank
`floor(m/2)` in increasing order.

[TailMedian.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/TailMedian.lean)
defines the median and proves two counting facts. If more than half of the
values are at least `a`, so is the median; if more than half are at most `c`,
so is the median. The median certificate lies in `(0,1]`. With a common flip
budget `b` the `m` probes are charged at most `m b` flips on every stream.

[TailMedianProbability.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/TailMedianProbability.lean)
proves the amplification. Along independent blocks, the indicators of a set
form a Bernoulli tape, so the project's Hoeffding bound for tape prefixes
applies to them. A set of probability at least `3/4` therefore contains more
than half of the first `m` blocks, except with probability `exp(-m/8)`. Applied
to the coverage event and to the performance event of one probe, a union bound
gives both for the median except with probability `2 exp(-m/8)`, which is at
most `delta` when `m >= 8 log(2/delta)`. The two events are not assumed
independent. A second union bound handles every depth `J >= 1` at once, when
the failure event of depth `J` has probability at most `delta/(J(J+1))`.

[TailMedianLaw.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/TailMedianLaw.lean)
states the results for every probability law `mu` of positive gaps and every
measurable gap-dependent sign law. For `m >= 8 log(2/delta)` probes with flip
budget `4^J` each, with probability at least `1 - delta`,
`F(2^-J) <= U <= min(1, 128 max(u_J, W_J/4^J))`. This is statement (1) of the
tail certificate. The lower bound holds for every choice of the probes' flip
budgets and coin caps, so it also covers a procedure that is paused part of the
way through. With a common budget `b` and coin cap `M` the upper bound is
`min(1, 128 max(u_J, W_J/b, 1/M))`. With `m_J >= 8 log(2 J (J+1)/delta)` probes
at depth `J`, both bounds hold at every depth `J >= 1` at once with probability
at least `1 - delta`.

The probes of one depth, and the probes of all depths, can draw disjoint coins
of one coin array. Splitting a sequence of independent coins by the pairing
function gives independent streams, and statement (1) and the all-depth
statement are also proved in that form, on the coin array of the original
simulation law.

Run `python tools/verify_arbitrary_law_tail_median.py` for 51 exact statements
and 51 transitive axiom reports, one for each declaration of the three
modules. The audit fails if a declaration is added without being registered.
The [tail-median record](../results/arbitrary-law-tail-median-20261111/README.md)
identifies the proof checkpoint and source hashes.

The oracle comparison (3) is the subject of the next section. The pilot of
(A6) to (A8), which uses a common number of probes, the caps `b_j` and `M`,
and a finite union over depths, is the subject of
[a later section](#capped-multi-depth-pilot). The probes are defined on
streams of tapes; their readers of observed flips are the subject of
[a later section](#tail-certificate-in-the-observable-experiment).

## Oracle comparison of the tail certificate

This is the
[comparison with the rare-event oracle](ARBITRARY_LAW_TAIL.md#comparison-with-the-rare-event-oracle),
statement (3) of the tail certificate. `K` below is the entropy-tail selection
functional `K_(mu,rho)(B)` of the rare-event theory, with its cap at `rho` and
its infimum over all submeasures.

[TailOracle.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/TailOracle.lean)
works with one kernel: the unresolved probability of a coin of gap `d` plus its
work envelope over `N = 4^J`. Its integral over the gap law is `u_J + W_J/N`.
With `t = 2^-J`, the kernel is at most `2052 min(1, t/d)` on every gap, and at
most `(1024 (J+1) + 16) t^2/a^2` on gaps at least `a`. The gap law is split at
its lowest-gap quantile of mass `rho`, with a fraction of a boundary atom when
needed. The existing quantile-tail floor bounds the quantile part by `2052 K`.
The core has gaps at least the quantile threshold `a > 0`. The onset condition
at depth `J` is `2048 (J+1) 2^-J / a^2 <= sqrt(rho)`. Under it the core part is
at most `t sqrt(rho)`, which the existing objective floor bounds by `K/2`.
Hence `u_J + W_J/N <= 4096 K(4^J)`, and the bound of statement (1) is at most
`524288 K(4^J)`. The onset condition holds at every large depth.

[TailOracleLaw.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/TailOracleLaw.lean)
states the result for the median certificate `U`, for every probability law
`mu` of positive gaps, every measurable gap-dependent sign law and
`0 < rho <= 1/4`. With probability at least `1 - delta`,
`F(2^-J) <= U <= 524288 K(4^J)` at every depth that meets the onset condition.
There is a finite onset `J0`, depending on `mu` and `rho` only, past which
every depth meets it. The procedure receives neither `rho` nor the onset. The
statement is given on independent streams and on one coin array, at one depth
and at every depth at once with `m_J >= 8 log(2 J (J+1)/delta)` probes.

No inverse moment or tail regularity of the law is assumed. The onset is
large: for a point mass at `1/2` and `rho = 1/4` the condition first holds at
depth 19, which is `4^19` flips for each probe.

Run `python tools/verify_arbitrary_law_tail_oracle.py` for 26 exact statements
and 26 transitive axiom reports, one for each declaration of the two modules.
The audit fails if a declaration is added without being registered. The
[tail-oracle record](../results/arbitrary-law-tail-oracle-20261111/README.md)
identifies the proof checkpoint and source hashes.

With this section, statements (1) to (4) of the tail certificate are checked
for probes that read the coin array of the original experiment. The next
section runs those probes as readers of observed flips.

## Tail certificate in the observable experiment

The sections above define the probes on the coin array of the original
experiment. Here a **reader** runs them: a rule that chooses the next coin to
flip from the flips observed so far. The estimator sees only flips, and its
certificate is a function of the observed word.

[TailProbeReader.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/TailProbeReader.lean)
gives the reader of one probe. A state machine tests coin 0, then coin 1, and
so on with the sign-neutral tail test, and keeps the probe's completed count:
the count freezes once an unresolved coin is completed or `M` coins are
counted. An invariant relates the state after `t` flips to the tape-level
probe on the same table of coin tapes. Hence the count computed from the
observed word equals `probeCompleted J t M` at every flip budget `t`. The word
at a smaller budget is a prefix of the word at a larger one, so the count can
be read from any prefix of a longer block. After `t` flips the reader is on
the first coin whose test is not complete within `t` flips: it buys the flips
of each coin consecutively and never returns to a coin. These statements are
pathwise.

[TailBlockReader.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/TailBlockReader.lean)
runs blocks one after another. Block `n` buys its flips with its own reader on
the coins `Nat.pair n i`; the part of the observed word that it bought is then
the word its reader would observe alone on those coins, and the coins of
blocks that have not run are untouched. With probe `j` as block `j`, the
median computed from the observed word of `m` blocks of `b` flips equals the
tape-level median certificate of probes reading the coins `Nat.pair j i`. Cut
after `t` flips, it equals the tape-level median with probe `j` at flip budget
`min(max(t - j b, 0), b)`: complete probes, at most one interrupted probe, and
probes that have not started. With one more level of blocks, depth `J` reads
the coins `Nat.pair J (Nat.pair j i)`.

[TailObservable.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/TailObservable.lean)
defines an estimator that buys a block of `n` flips with a reader and reports
a function of the observed word. It buys at most `n` flips on every admissible
path. Every event about the observed word has the same probability under the
law of the original hidden-gap experiment as the same event about the reader's
word on the coin array of the original simulation law. The coin-array
statements therefore hold for the estimator, for every probability law `mu`
of positive gaps and every measurable gap-dependent sign law:

- **Statement (1).** For `m >= 8 log(2/delta)` probes with `4^J` flips each,
  with probability at least `1 - delta` the output `U` is at most
  `min(1, 128 max(u_J, W_J/4^J))`, and the certificate computed from the first
  `t` observed flips is at least `F(2^-J)` for every `t` at once. With `b >= 1`
  flips and coin cap `M >= 1` the upper bound is
  `min(1, 128 max(u_J, W_J/b, 1/M))`.
- **Statement (3).** For `0 < rho <= 1/4`, at a depth that meets the onset
  condition the output is at most `524288 K(4^J)`, and every depth past a
  finite onset that depends on `mu` and `rho` only meets it.
- **Depths up to `L`.** One estimator runs the depths `J <= L` one after
  another, with `m_J >= 8 log(2 J (J+1)/delta)` probes at depth `J`. With
  probability at least `1 - delta` the bounds above hold at every depth
  `1 <= J <= L` at once.

The reader buys every block in full. Flips bought after a probe has stopped
are charged and ignored, so the estimator's charge is its cap, `m b` flips at
one depth. An estimator that stops buying when its probes stop is not
constructed.

Run `python tools/verify_arbitrary_law_tail_observable.py` for 68 exact
statements and 68 transitive axiom reports, one for each declaration of the
three modules. The audit fails if a declaration is added without being
registered. The
[tail-observable record](../results/arbitrary-law-tail-observable-20261111/README.md)
identifies the proof checkpoint and source hashes.

The pilot of (A6) to (A8) is the subject of the next section.

## Capped multi-depth pilot

This is the pilot of the
[adaptation proof](ARBITRARY_LAW_ADAPTATION.md#2-learning-the-envelope-under-one-physical-cap):
(A6) and (A8) to (A10). For a target depth `J >= 1` with `N = 4^J`, it runs a
common number `m` of probes at every depth `j = 1, ..., J`.

[TailPilot.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/TailPilot.lean)
defines the budgets `b_j = ceil(N/(2 j (j+1))) + 2^(J+j-2)` and the coin cap
`M = ceil(sqrt(64 N/rho))` of (A6). It proves (A10): `N/2 <= sum_j b_j <= N`
for every `J >= 1`, so the pilot buys `m sum_j b_j <= m N` flips. Block `i` of
its reader runs the `m` probes of depth `i + 1`, probe `k` on the coins
`Nat.pair i (Nat.pair k c)`. The certificate of each depth is computed from
the observed word, equals the tape-level median of the probes on those coins,
and lies in `(0, 1]`. At depth one no check can resolve a coin, so a depth-one
probe counts at most one coin and its certificate is one. This holds for every
word of flips, which the learning stage requires.

[TailPilotLaw.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/TailPilotLaw.lean)
proves the event (A8) for every probability law `mu` of positive gaps and
every measurable gap-dependent sign law. For `m >= 8 log(2J/epsilon)`, with
probability at least `1 - epsilon`,
`F(2^-j) <= U_j <= 128 (u_j + W_j/b_j + 1/M)` at every depth `1 <= j <= J` at
once. The union over depths is finite and uses the same number of probes at
every depth; the failure probability is at most `2 J exp(-m/8)`. The event is
proved in two settings:

- **The pilot alone.** An estimator that runs only the pilot buys at most
  `m sum_j b_j` flips on every admissible path, and (A8) holds for its
  certificates under the law of the original hidden-gap experiment.
- **The pilot in the learning stage.** The pilot is installed in the
  [observable learning stage](#observable-learning-stage). Its probes read the
  coins `Nat.pair 0 (Nat.pair i (Nat.pair k c))`, and the continuation reads
  the fresh coins `Nat.pair 1 i`. (A8) holds for the certificates the stage
  reads off the pilot's word, on the coin array of the original simulation
  law.

The stage's learned law is the finite law (A9). With `c_j` the prefix minima
of the certificates, it puts mass `c_J` at zero and mass `c_j - c_(j+1)` at
`2^-(j+1)`. It is a probability law on every observed word, and no latent
count of small gaps enters it. When the certificates cover `F(2^-j)` at every
depth, it dominates `mu` in distribution at every point; so it does on the
event (A8). The stage buys at most `m sum_j b_j` flips plus the continuation's
on every admissible path.

The reader buys every block in full, so the pilot is charged its cap. The
paper's remark that the coin cap lets easy-law pilots stop early is not
formalized. (A8) is stated under the law of the original experiment for the
pilot alone, and on the coin array for the stage.

Run `python tools/verify_arbitrary_law_pilot.py` for 66 exact statements and
66 transitive axiom reports, one for each declaration of the two modules. The
audit fails if a declaration is added without being registered. The
[pilot record](../results/arbitrary-law-pilot-20261111/README.md) identifies
the proof checkpoint and source hashes.

The learned law's comparison with the oracle past its onset, (A11) to (A14),
is in the next two sections.

## Learned law against the oracle: work estimates and onset

This is the first part of
[section 3 of the adaptation proof](ARBITRARY_LAW_ADAPTATION.md#3-the-learned-law-retains-the-oracle-rate):
the split of the gap law, the estimate (A12), the onset, and the two floors
that (A14) uses. `K` is the entropy-tail selection functional
`K_(mu,rho)(4^J)`.

[PilotOnset.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/PilotOnset.lean)
splits the gap law at its lowest-gap quantile of mass `rho`, `mu = nu + sigma`,
with a fraction of a boundary atom when needed. The quantile part `nu` has
mass `rho`, and the core `sigma` has gaps at least the quantile threshold
`a > 0`. This is the project's existing quantile split; the module collects
its properties in one statement. For the pilot of target depth `J`, with
`t = 2^-J` and the budgets `b_j` of (A6), every depth `1 <= j <= J` satisfies

- `W_(j,nu)/b_j <= 8192 tau_nu(t)`, and
- `W_(j,sigma)/b_j <= 2048 (J+1)^3 t^2/a^2`,

where `W_(j,.)` integrates the work envelope of depth `j` and `tau_nu` is the
tail modulus. This is (A12). The first bound uses the geometric part
`2^(J+j-2)` of the budget and the scaling `tau_nu(s) <= (s/t) tau_nu(t)`; the
second uses the reciprocal part.

The pilot's onset condition at depth `J` is
`2048 (J+1)^3 2^-J / a^2 <= sqrt(rho)`. It holds at every large depth, and it
implies the onset condition of the tail certificate. Under it, for
`0 < rho <= 1/4`: `W_j/b_j <= 8193 K` at every depth of the pilot,
`2 t sqrt(rho) <= K`, and the coin cap satisfies `16/M <= K`. The threshold `a`
and the onset are proof quantities; the pilot receives neither. The onset is
large: for a point mass at `1/2` and `rho = 1/4` the condition first holds at
depth 29.

Run `python tools/verify_arbitrary_law_pilot_onset.py` for 25 exact statements
and 25 transitive axiom reports, one for each declaration of the module. The
audit fails if a declaration is added without being registered. The
[pilot-onset record](../results/arbitrary-law-pilot-onset-20261111/README.md)
identifies the proof checkpoint and source hashes.

The rest of (A11) is in the next section.

## Learned law against the oracle: the comparison

This is the second part of
[section 3 of the adaptation proof](ARBITRARY_LAW_ADAPTATION.md#3-the-learned-law-retains-the-oracle-rate):
(A13), (A14), the clipped-CDF witness and (A11). `U_1 = 1, U_2, ..., U_J` are
nonnegative certificates, `c_j` their prefix minima and `mu_bar` the learned
law (A9). The upper half of (A8) is `U_j <= 128 (u_j + W_j/b_j + 1/M)` at
every depth `1 <= j <= J`.

[LearnedCDF.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/LearnedCDF.lean)
defines `mu' = L(V D / 2)`, the gap times the independent light multiplier of
the contraction, divided by two. The terminal estimate of the tail test gives
`u_j <= F_(mu')(2^-(j+1))`. Under the upper half of (A8), at every real `x`,

- `F_(mu_bar)(x) <= min(1, 128 F_(mu')(x) + e)`, with `e = 128 w + 128/M + c_J`,

where `w = 8192 tau_nu(t) + 2048 (J+1)^3 t^2/a^2` is the bound of (A12) on
`W_j/b_j` at every depth. This is (A13), with `w` in place of the maximum
over depths; it needs no onset. Under the pilot's onset condition and
`0 < rho <= 1/4`, `w <= 8193 K`, and when `U_J` satisfies the upper half of
(A8), `e <= 2621712 K`. There `K` is positive and finite, so `e < 2^22 K`.
This is (A14).

[LearnedOracle.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/LearnedOracle.lean)
proves that the lowest-gap quantile part of mass `r` of a law `eta` has
distribution function `min(r, F_eta)`. The witness `lambda` for a law `eta`
of positive gaps and `e >= 0` is the unit mass at zero when `e >= 1`, and
otherwise mass `e` at zero plus 128 times the quantile part of `eta` of mass
`(1 - e)/128`. It is a probability law dominated by `128 eta + e delta_0`,
and `F_lambda(x) = min(1, 128 F_eta(x) + e)` for every `x >= 0`. With
`eta = mu'`, (A13) says that `lambda` lies below `mu_bar` in the distribution
order, and

- `K_(mu_bar) <= sqrt(3) K_lambda <= 2 (128 K_(mu') + e) <= 2 (4096 + 2^22) K`,

by the CDF comparison, dominated mass, the light contraction and (A14). So
under the onset condition and the upper half of (A8),
`K_(mu_bar,rho)(4^J) <= 2^24 K_(mu,rho)(4^J)`, which is (A11). `K_(mu_bar)` is
the selection functional extended to laws with mass at zero, with the
infimum over all fractional selections. There is a depth `J_0 >= 1`,
depending on the gap law and `rho` only, such that (A11) holds at every
`J >= J_0`.

For the pilot installed in the learning stage with `m >= 8 log(2J/eps)`
probes at every depth, under the onset condition: with probability at least
`1 - eps` on the coin array of the original simulation law, the stage's
learned law dominates the gap law in distribution and satisfies (A11). This
holds at every `J >= J_0`, for every measurable gap-dependent sign law and
every stage. `V`, `mu'`, `lambda`, `e`, the threshold `a` and the onset are
proof quantities; the pilot neither samples nor computes them.

Run `python tools/verify_arbitrary_law_learned_oracle.py` for 31 exact
statements and 31 transitive axiom reports, one for each declaration of the
two modules. The audit fails if a declaration is added without being
registered. The
[learned-oracle record](../results/arbitrary-law-learned-oracle-20261111/README.md)
identifies the proof checkpoint and source hashes.

The event is stated on the coin array, as (A8) is, not under the law of the
experiment of the whole stage.

## Quantile design with a zero atom

This is (A16) of
[section 4 of the adaptation proof](ARBITRARY_LAW_ADAPTATION.md#4-robust-use-of-the-known-law-estimator).
A reference law with unresolved mass is `alpha = z delta_0 + (1 - z) eta`,
with `eta` a probability law of positive gaps.
[ZeroQuantile.lean](../lean/ThresholdHC/ArbitraryLawAdaptation/ZeroQuantile.lean)
defines its quantile design value. The design removes the zero atom and the
lowest-gap mass `rho - z` of the positive part, which under `eta` is the
quantile part `nu` of mass `r = (rho - z)/(1 - z)`; `sigma` is the remaining
quantile core. With `h = B^(-1/2)`,

- `Q_alpha = min(rho, z + (1 - z) tau_nu(h) + h sqrt(rho (1 - z) Gamma_sigma))`
  for `z < rho`, and `Q_alpha = rho` for `z >= rho`.

For every probability law `alpha` on `[0, 1/2]`, the module proves that
`alpha` has this form with `z = alpha{0}` and `eta` its normalized positive
part when `alpha{0} < 1`, and that

- `K_alpha <= Q_alpha <= 4 K_alpha` for `0 < rho <= 1/4` and `B > 0`,

where `K_alpha` is the selection functional extended to laws with mass at
zero. The lower bound holds for `rho <= 1` and every `B`: for `z < rho` the
second term of `Q_alpha` is the selection objective at the admissible
selection `(1 - z) sigma`. The upper bound uses the zero floor
`K_alpha >= min(rho, z)`, the scaling `K_alpha >= (1 - z) K_(eta,r)`, the
bound `Q_alpha <= z + sqrt(2) (1 - z) Q_(eta,r)` for `z <= rho/2` in both cap
cases, and the positive-gap 8/5 comparison. Without a zero atom `Q_alpha` is
the closed quantile value.

Run `python tools/verify_arbitrary_law_zero_quantile.py` for 22 exact
statements and 22 transitive axiom reports, one for each declaration of the
module. The audit fails if a declaration is added without being registered.
The [zero-quantile record](../results/arbitrary-law-zero-quantile-20261112/README.md)
identifies the proof checkpoint and source hashes.

The plan that uses this design is specified in the next section, and its
rate for exact integrals in the one after. The coefficients `C_0` and `C_*`
are not formalized.

## Known-law plan and its certificate

The [known-law estimator](KNOWN_LAW_ESTIMATOR.md#work-and-error-of-a-returned-plan)
plans from a split `sigma + tau + zeta` of its gap law: the selected core, the
resolved tail and the unresolved part. A plan has a terminal level `J`, a cap
`4^(kappa_l)` and a price `C_l` for each level, and positive mean counts
`r_l`. With `delta_l = rho 16^-(l+1)`, its certificate is
`delta_J^2 + sum_l 17 delta_l / r_l`. The modules in
[KnownLawPlanner](../lean/ThresholdHC/KnownLawPlanner/PlanCertificate.lean)
specify the plan and prove the certificate for the level price of the checked
upper theorem.

- [PlanFamily.lean](../lean/ThresholdHC/KnownLawPlanner/PlanFamily.lean) runs
  the race of level `l` at any cap whose resolved error is at most
  `delta_l/8`. Its bias is at most `delta_l`, a correction has second moment
  at most `17 delta_l`, and its expected work is at most the level price
  `min(2 4^k, 128 (l+1) Gamma + 6 H^2/rho + 2 O_tau(4^k) + 2 z 4^k)`.
- [PlannedEstimator.lean](../lean/ThresholdHC/KnownLawPlanner/PlannedEstimator.lean)
  runs the Poisson multilevel estimator with any positive rates.
- [PlanCaps.lean](../lean/ThresholdHC/KnownLawPlanner/PlanCaps.lean) is the
  cap search: from the cap 4, multiply by four until an error envelope is at
  most `delta_l/8`, and carry the cap to the next level. It states the
  termination requirement on the envelope and proves that the exact resolved
  error of a finite measure meets it.
- [PlanAllocation.lean](../lean/ThresholdHC/KnownLawPlanner/PlanAllocation.lean)
  turns weights into mean counts `n_i = B w_i / sum_j k_j w_j`. They spend the
  budget exactly, and weights within a factor `theta` of `sqrt(v_i/k_i)` cost
  at most that factor in the variance term.
- [PlanCertificate.lean](../lean/ThresholdHC/KnownLawPlanner/PlanCertificate.lean)
  defines enclosures, upper bounds of the five design integrals, and proves:
  a plan whose caps pass the test against the enclosure's envelope, whose
  terminal level has `delta_J/8` at least the enclosure's unresolved mass and
  whose counts are priced by the enclosure spends at most `B` in expectation
  and has squared risk at most its certificate, under every rare prior. The
  plan with the searched caps and counts from any positive weights is such a
  plan.

The estimator observes flips only. The statements hold for every plan that
meets the conditions, so they cover a planner that works from upper bounds.
They do not cover the toolkit's planner as written: it uses the smaller price
`80 (l+2) G-bar + 4 H^2/rho`, rounds its counts at random, and runs the
coarse race of a correction on further flips of the same coin.

Run `python tools/verify_known_law_planner.py` for 49 exact statements and 49
transitive axiom reports, one for each declaration of the five modules. The
audit fails if a declaration is added without being registered. The
[planner record](../results/known-law-planner-20261112/README.md) identifies
the proof checkpoint and source hashes.

The plan's rate is in the next section.

## Rate of the exact known-law plan

Let the plan use the quantile split of its gap law `mu`: the core `sigma` is
the quantile core at rarity `rho`, and the quantile part is cut at
`h = B^(-1/2)` into the resolved tail, on gaps at least `h`, and the
unresolved part, on gaps at most `h`, of mass `z`. Let it take the exact
resolved error as its envelope and the exact integrals in its prices.

[PlanRate.lean](../lean/ThresholdHC/KnownLawPlanner/PlanRate.lean) proves that
the carried cap search then returns the least admissible cap of each level,
so each price is at most the level work certificate of the upper theorem and
`sum_(l <= J) sqrt(17 delta_l k_l) <= 28000 (sqrt(rho Gamma) + H)`. The
terminal rule stops at the first level `J` with `delta_J/16` below
`max(128 z, rho/(16 (1 + sqrt B)))`. Outside the constant fallback,
`2048 z <= rho`, that level has `z <= delta_J/128`, and
`delta_J < 2048 z + rho/(1 + sqrt B)`. With weights within a factor `theta`
of the optimal ones, the square root of the certificate is at most
`delta_J + sqrt(theta) 28000 (sqrt(rho Gamma) + H)/sqrt B`.

[PlanQuantileRate.lean](../lean/ThresholdHC/KnownLawPlanner/PlanQuantileRate.lean)
proves the floor `rho/(1 + sqrt B) <= K` at every budget and compares with the
selection functional `K = K_(mu,rho)(B)`:

- `min(rho/2, sqrt(certificate)) <= (1 + (8/5) max(2048, 28000 sqrt(theta))) K`,
  and the constant `rho/2` of the fallback obeys the same bound;
- a radius `r <= kappa sqrt(8 min(rho^2/4, certificate))` with
  `kappa sqrt(8) <= 6` is at most six times that coefficient times `K`.

For `theta = 2` the two coefficients are below 63,358 and 380,148. The radius
statement holds for every relative upper square root. These are the
coefficients for exact integrals and a law of positive gaps. The coefficients
`C_0 = 1 + 4 max(4096, 8 sqrt(2) C_sum)` and `C_* = 6 C_0` of the adaptation
proof, for a planner that works from upper bounds within a factor two and for
a reference law with mass at zero, are in the next section.

Run `python tools/verify_known_law_plan_rate.py` for 18 exact statements and
18 transitive axiom reports, one for each declaration of the two modules. The
audit fails if a declaration is added without being registered. The
[plan-rate record](../results/known-law-plan-rate-20261112/README.md)
identifies the proof checkpoint and source hashes.

## Rate of a plan computed from upper bounds

The planner does not have the exact design integrals. An enclosure is tight
when its bounds for `H`, the unresolved mass, the resolved error and the
ordinary work are at most twice the true quantities, and its entropy bound is
at most four times the entropy; the last two bounds are needed at the powers
of four only. The unresolved mass `z` of the design is a parameter: the mass
of the unresolved part for a law of positive gaps, and that mass plus the mass
at zero for a reference law that has one.

[PlanTightRate.lean](../lean/ThresholdHC/KnownLawPlanner/PlanTightRate.lean)
proves that band costs within a factor two give a cost entropy within a
factor two, that the searched cap of level `l` is at most the least
admissible cap of level `l+1`, and that the price of level `l` is at most
four times the level work certificate of level `l+1`. With
`delta_l = 16 delta_(l+1)` the multilevel sum of the upper theorem gives
`sum_(l <= J) sqrt(17 delta_l k_l) <= 8 * 28000 (sqrt(rho Gamma) + H)` for a
terminal level with `z <= delta_J/128`. The planner chooses the terminal
level from its bound `z-bar` and falls back to the constant when
`2048 z-bar > rho`; otherwise `z <= delta_J/128` and
`delta_J < 4096 z + rho/(1 + sqrt B)`. None of these statements needs the
split to be a probability measure.

[PlanTightQuantileRate.lean](../lean/ThresholdHC/KnownLawPlanner/PlanTightQuantileRate.lean)
gives the rate for the quantile split of a law of positive gaps:
`min(rho/2, sqrt(certificate)) <= (1 + (8/5) max(4096, 224000 sqrt(theta))) K`,
with the same bound for the fallback constant and six times the coefficient
for the radius.

[PlanZeroAtomRate.lean](../lean/ThresholdHC/KnownLawPlanner/PlanZeroAtomRate.lean)
treats a reference law `alpha = z_0 delta_0 + (1 - z_0) eta`. The split is the
quantile split of `eta` at the conditional rarity `(rho - z_0)/(1 - z_0)`,
scaled by `1 - z_0`, and the mass at zero is part of the unresolved mass
`z`. Then:

- `rho/(1 + sqrt B) <= K_alpha` for `rho <= 1/2`;
- for `z_0 < rho` the [zero-atom quantile value](#quantile-design-with-a-zero-atom)
  is `min(rho, z + h H + h sqrt(rho Gamma_sigma))`, so the capped design value
  is at most `4 K_alpha` by (A16);
- `min(rho/2, sqrt(certificate)) <= (1 + 4 max(4096, 224000 sqrt(theta))) K_alpha`
  outside the fallback, and the constant `rho/2` obeys the same bound when
  `2048 z-bar > rho`, for every `z_0 >= 0`;
- for upper square roots within a factor two this coefficient is
  `C_0 = 1 + 4 max(4096, 8 sqrt(2) C_sum)` at `C_sum = 28000`, and the radius
  is at most `6 C_0 K_alpha`. `C_0` does not decrease with `C_sum`, so the
  bounds also hold with the paper's value at `C_sum = 30000`.

These are statements about the numbers the planner computes. The experiment
of the upper theorem has positive gaps only, so the estimator of a reference
law with mass at zero, with the fair-coin likelihood its bank uses for that
mass, is not formalized. Nor is the rational arithmetic that produces a tight
enclosure for a finite law.

Run `python tools/verify_known_law_plan_tight_rate.py` for 31 exact statements
and 31 transitive axiom reports, one for each declaration of the three
modules. The audit fails if a declaration is added without being registered.
The [tight-rate record](../results/known-law-plan-tight-rate-20261112/README.md)
identifies the proof checkpoint and source hashes.

## Output of the planner end to end

The rate theorems of the two sections above are stated for a split with
hypotheses that identify it as the quantile split cut at the budget scale.
[PlannerOutput.lean](../lean/ThresholdHC/KnownLawPlanner/PlannerOutput.lean)
constructs that split for every probability law of positive gaps, so the
hypotheses can be met, and joins the validity of the plan to its rate:

- for an enclosure whose envelope meets the termination requirement, the
  minimax risk at budget `B` is at most `min(rho/2, sqrt(certificate))`;
- for every tight enclosure of the quantile split and weights within a factor
  `theta`, the planner's output, the plan when `2048 z-bar <= rho` and the
  constant otherwise, gives minimax risk at most
  `(1 + (8/5) max(4096, 224000 sqrt(theta))) K`;
- with the exact integrals and the optimal weights, for every probability law
  `mu` of positive gaps, `0 < rho <= 1/4` and `B > 0`, the minimax risk is at
  most `44801 K_(mu,rho)(B)`.

The existing upper theorem bounds the minimax risk by 28000 times the
selection value of every selection, with an estimator that runs each level
at its least admissible cap. The statement here is for the output of the
specified planner. For a reference law with mass at zero the module
constructs the scaled quantile split and shows that its exact integrals, with
the mass at zero added to the unresolved mass, are a tight enclosure.

Run `python tools/verify_known_law_planner_output.py` for 9 exact statements
and 9 transitive axiom reports, one for each declaration of the module. The
audit fails if a declaration is added without being registered. The
[planner-output record](../results/known-law-planner-output-20261112/README.md)
identifies the proof checkpoint and source hashes.

## Robust continuation: the race is monotone and its error transfers

The robust continuation runs the estimator designed from a reference law
under a true law with larger gaps. Its first step is checked in
[four modules](../lean/ThresholdHC/RobustContinuation/RobustLevelError.lean).

Tapes of flips are ordered pointwise, with tails below heads. Flips built
from common uniforms are monotone in the success probability, so an upper
set of tapes is at least as likely under the coin with the larger success
probability
([TapeOrder.lean](../lean/ThresholdHC/RobustContinuation/TapeOrder.lean)).
With more heads, a positive decision of the ordinary classifier stays
positive and is not delayed, and a strictly earlier stop is a positive
decision; a terminal tie is negative
([ClassifierOrder.lean](../lean/ThresholdHC/RobustContinuation/ClassifierOrder.lean)).

[RaceOrder.lean](../lean/ThresholdHC/RobustContinuation/RaceOrder.lean) calls
a prefix test downward when turning tails into heads cannot make it fire, and
upward when that cannot stop it from firing. For a downward negative test and
an upward positive test the output of the race is monotone in the flips. The
negative bank is downward and the positive bank is upward, for every
reference law. Hence the error of the race on a coin of either sign does not
increase when the gap grows.

[RobustLevelError.lean](../lean/ThresholdHC/RobustContinuation/RobustLevelError.lean)
transfers the population error. Let `pi` be a finite measure on pairs of
gaps with `z_1 <= z_2` almost everywhere, and let the true law be its second
marginal plus a finite part `mu_0`. Then for every sign law `q` of the true
gaps:

- the population error of the race is at most
  `int [q(z_2) e_+(z_1) + (1 - q(z_2)) e_-(z_1)] d pi + mu_0(all gaps)`, where
  `e_+` and `e_-` are its errors on one coin;
- for the bank designed from a probability law `eta` with allowances
  `eps` and `u`, when the first marginal of `pi` is `c eta` and `q` has
  positive fraction at most `rho` under the true law, the error at cap `2^L`
  is at most `rho eps + c u + c int min(1, (2^L d^2)^-2) d eta + mu_0(all gaps)`.

The integral in the first statement is the error under the sign allocation
that the coupling induces on the reference gaps, written without a
conditional expectation. A reference law `z_0 delta_0 + (1 - z_0) eta` is
the case `c = 1 - z_0` with `mu_0` the part of the true law coupled to the
atom: its mass is charged in full, the positive bank's null law is that of
`eta`, and no coin of gap zero is used.

The coupling is a hypothesis here. The work of the race is in the next
section: increasing a gap can remove a wrong early exit, so the stopping
time is not monotone.

Run `python tools/verify_robust_error_transfer.py` for 33 exact statements and
33 transitive axiom reports, one for each declaration of the four modules.
The audit fails if a declaration is added without being registered. The
[robust-error record](../results/robust-error-transfer-20261113/README.md)
identifies the proof checkpoint and source hashes.

## Robust continuation: work on a coin with a larger gap

The stopping time of the race is not monotone in the flips, so its work does
not transfer the way its error does.
[RobustCoinWork.lean](../lean/ThresholdHC/RobustContinuation/RobustCoinWork.lean)
proves instead that each of the three work bounds of the known-law theorem
holds at a reference gap `d_0` for a coin of every gap `d >= d_0`:

- the ordinary work kernel `min(M, 17 d^-2 (1 + log+(M d^2)))` does not
  increase with the gap, so the work of any race is at most twice the kernel
  at `d_0`;
- for a negative coin and a reference gap `d_0` in band `j`, the work of the
  bank race is at most `(3/(2 d_0^2)) (1 + log(1/(eps w_j)))`: the race stops
  by the crossing time of the matching negative reference, and the drift of
  its score increases with the gap of the coin;
- for a positive coin, the race is still running after `n` rounds with
  probability at most `exp(-n d_0^2/2)`, and its work is at most
  `12 A(d_0)/d_0^2` with the three-piece surcharge at `d_0`: the race has
  stopped once the running mean of the bank's flips is above `1/2 + d_0/2`,
  and a low running mean is a lower set of tapes.

No crossing time that ignores wrong exits is needed. The bounds are for one
coin. Integrating them over a true law coupled above the reference, with the
rarity budget of the induced sign allocation, is not done here.

Run `python tools/verify_robust_coin_work.py` for 9 exact statements and 9
transitive axiom reports, one for each declaration of the module. The audit
fails if a declaration is added without being registered. The
[robust-work record](../results/robust-coin-work-20261113/README.md)
identifies the proof checkpoint and source hashes. Across all twenty-six
current component audits, 834 exact statements and 832 transitive axiom
reports pass.

## Work still needed for the full theorem

CDF domination now gives an increasing coupling and the selection
comparison, including unresolved mass at zero. Dominated mass and the concrete
factor-32 light random contraction are also checked. The finite
CDF envelope is checked, and the capped multi-depth pilot now supplies its
statistical event; its law-dependent onset is checked. The single-coin
tail test, one capped probe over fresh
coins, the median over independent probes, its form at every depth and its
oracle comparison past the onset are checked, on the coin array and for an
estimator that reads only observed flips; so is the multi-depth pilot built
from them. The observable stage is checked as an execution component with
the concrete pilot installed, and the learned law's oracle comparison is
checked past its finite onset, on the coin array. The quantile design of a
law with mass at zero is compared with the selection functional, and the
certificate of a known-law plan is checked for the level price of the upper
theorem. Its rate is checked for exact integrals and for upper bounds within
a factor two, including the design of a reference law with mass at zero.
A tight enclosure must be computed for finite laws. For the robust
continuation, the race is monotone in the flips and its population error
transfers to a true law coupled above the reference, with mass at zero in
the reference charged in full and no coin of gap zero. Its work bounds on
one coin hold at the reference gap for every larger gap. The coupling with
its induced sign allocation, the level work under the coupling, the
corrections and the plan under the true law, the physical-cap median and
the connection to the paid stage must still be proved. Finally the stages need to be joined into the
all-budget controller, with fresh stages, nested intervals, simultaneous
coverage and eventual oracle width. These conclusions must be proved, not
supplied as assumptions to a controller interface.
