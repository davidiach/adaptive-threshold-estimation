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
bounds; the pilot's probability guarantee for those bounds remains to be proved.

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
does not instantiate the statistical pilot or robust continuation, or assume
their desired risk bounds in place of proving them. It is a single stage,
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

These are statements about one coin. They do not include fresh-coin inverse
sampling, the median over probes, the multi-depth pilot or the onset, and the
test is not yet embedded as a reader in the observable stage. Across all
twelve current component audits, 327 exact statements and 325 transitive axiom
reports pass.

## Work still needed for the full theorem

CDF domination now gives an increasing coupling and the selection
comparison, including unresolved mass at zero. Dominated mass and the concrete
factor-32 light random contraction are also checked. The finite
CDF envelope is checked, but still needs its statistical pilot event and
law-dependent onset. The single-coin tail test is checked with its error and
work bounds; capped inverse sampling over fresh coins, the median, and the
multi-depth pilot built from it are not. The observable stage is checked as an execution component;
the concrete pilot and robust continuation must be instantiated and their
statistical bounds proved. Finally the stages need to be joined into the
all-budget controller, with fresh stages, nested intervals, simultaneous
coverage and eventual oracle width. These conclusions must be proved, not
supplied as assumptions to a controller interface.
